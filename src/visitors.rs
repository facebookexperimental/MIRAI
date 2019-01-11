// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use abstract_domains::{AbstractDomains, ExpressionDomain};
use abstract_value::{self, AbstractValue, Path, PathSelector};
use constant_value::{ConstantValue, ConstantValueCache};
use environment::Environment;
use rpds::List;
use rustc::session::Session;
use rustc::ty::{LazyConst, Ty, TyCtxt, TyKind, UserTypeAnnotationIndex};
use rustc::{hir, mir};
use std::borrow::Borrow;
use std::collections::HashMap;
use summaries;
use summaries::PersistentSummaryCache;
use syntax::errors::{Diagnostic, DiagnosticBuilder};
use syntax_pos;

pub struct MirVisitorCrateContext<'a, 'b: 'a, 'tcx: 'b> {
    /// A place where diagnostic messages can be buffered by the test harness.
    pub buffered_diagnostics: &'a mut Vec<Diagnostic>,
    /// A call back that the test harness can use to buffer the diagnostic message.
    /// By default this just calls emit on the diagnostic.
    pub emit_diagnostic: fn(&mut DiagnosticBuilder, buf: &mut Vec<Diagnostic>) -> (),
    pub session: &'tcx Session,
    pub tcx: TyCtxt<'b, 'tcx, 'tcx>,
    pub def_id: hir::def_id::DefId,
    pub mir: &'a mir::Mir<'tcx>,
    pub constant_value_cache: &'a mut ConstantValueCache,
    pub summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,
}

/// Holds the state for the MIR test visitor.
pub struct MirVisitor<'a, 'b: 'a, 'tcx: 'b> {
    buffered_diagnostics: &'a mut Vec<Diagnostic>,
    emit_diagnostic: fn(&mut DiagnosticBuilder, buf: &mut Vec<Diagnostic>) -> (),
    session: &'tcx Session,
    tcx: TyCtxt<'b, 'tcx, 'tcx>,
    def_id: hir::def_id::DefId,
    mir: &'a mir::Mir<'tcx>,
    constant_value_cache: &'a mut ConstantValueCache,
    summary_cache: &'a mut PersistentSummaryCache<'b, 'tcx>,

    check_for_errors: bool,
    current_environment: Environment,
    current_span: syntax_pos::Span,
    exit_environment: Environment,
    inferred_preconditions: List<AbstractValue>,
    path_conditions: List<AbstractValue>,
    post_conditions: List<AbstractValue>,
    preconditions: List<AbstractValue>,
    unwind_condition: List<AbstractValue>,
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'a, 'b: 'a, 'tcx: 'b> MirVisitor<'a, 'b, 'tcx> {
    pub fn new(crate_context: MirVisitorCrateContext<'a, 'b, 'tcx>) -> MirVisitor<'a, 'b, 'tcx> {
        MirVisitor {
            buffered_diagnostics: crate_context.buffered_diagnostics,
            emit_diagnostic: crate_context.emit_diagnostic,
            session: crate_context.session,
            tcx: crate_context.tcx,
            def_id: crate_context.def_id,
            mir: crate_context.mir,
            constant_value_cache: crate_context.constant_value_cache,
            summary_cache: crate_context.summary_cache,

            check_for_errors: false,
            current_environment: Environment::default(),
            current_span: syntax_pos::DUMMY_SP,
            exit_environment: Environment::default(),
            inferred_preconditions: List::new(),
            path_conditions: List::new(),
            post_conditions: List::new(),
            preconditions: List::new(),
            unwind_condition: List::new(),
        }
    }

    /// Use the local and global environments to resolve Path to an abstract value.
    /// For now, statics and promoted constants just return Top.
    /// If a local value cannot be found the result is Bottom.
    fn lookup_path_and_refine_result(&mut self, path: Path) -> AbstractValue {
        let refined_val = {
            let bottom = abstract_value::BOTTOM;
            let local_val = self.current_environment.value_at(&path).unwrap_or(&bottom);
            local_val.refine_with(&self.path_conditions, self.current_span)
        };
        if refined_val.is_bottom() {
            // Not found locally, so try statics and promoted constants
            let mut val: Option<AbstractValue> = None;
            if let Path::StaticVariable { ref name } = path {
                let summary = self.summary_cache.get_persistent_summary_for(name);
                val = Some(summary.result.unwrap_or_else(|| abstract_value::TOP));
            }
            if let Path::PromotedConstant { .. } = path {
                // todo: #34 provide a crate level environment for storing promoted constants
                val = Some(abstract_value::TOP);
            }
            // This bit of awkwardness is needed so that we can move path into the environment.
            // Hopefully LLVM will optimize this away.
            if let Some(val) = val {
                self.current_environment.update_value_at(path, val.clone());
                return val;
            }
        }
        refined_val
    }

    /// Analyze the body and store a summary of its behavior in self.summary_cache.
    pub fn visit_body(&mut self) {
        debug!("visit_body({:?})", self.def_id);
        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<rustc::mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<rustc::mir::BasicBlock, Environment> = HashMap::new();
        // The entry block has no predecessors and its initial state is the function parameters.
        let mut first_block = true;
        for bb in self.mir.basic_blocks().indices() {
            let i_state = if first_block {
                first_block = false;
                Environment::with_parameters(self.mir.arg_count)
            } else {
                Environment::default() // Will be joined with other states before analysis of bb
            };
            in_state.insert(bb, i_state);
            out_state.insert(bb, Environment::default());
        }

        // Compute a fixed point, which is a value of out_state that will not grow with more iterations.
        let mut changed = true;
        let mut iteration_count = 0;
        while changed {
            changed = false;
            for bb in self.mir.basic_blocks().indices() {
                // Merge output states of predcessors of bb
                let mut i_state = Environment::default();
                for pred_bb in self.mir.predecessors_for(bb).iter() {
                    // todo: obtain join condition from analysis of pred_bb
                    let join_condition = &abstract_value::TOP;
                    // Once all paths have already been analyzed for a second time (iteration_count >= 3)
                    // we to abstract more aggressively in order to ensure reaching a fixed point.
                    if iteration_count < 3 {
                        i_state = i_state.join(&out_state[pred_bb], join_condition);
                    } else {
                        i_state = i_state.widen(&out_state[pred_bb], join_condition);
                    }
                }

                // Analyze the basic block.
                self.current_environment = i_state;
                self.visit_basic_block(bb);

                // Check for a fixed point.
                if !self.current_environment.subset(&out_state[&bb]) {
                    // There is some path for which self.current_environment.value_at(path) includes
                    // a value this is not present in out_state[bb].value_at(path), so any block
                    // that used out_state[bb] as part of its input state now needs to get reanalyzed.
                    out_state.insert(bb, self.current_environment.clone());
                    changed = true;
                } else {
                    // If the environment at the end of this block does not have any new values,
                    // we have reached a fixed point for this block.
                }
            }
            iteration_count += 1;
        }

        // Now traverse the blocks again, doing checks and emitting diagnostics.
        // in_state[bb] is now complete for every basic block bb in the body.
        self.check_for_errors = true;
        for bb in self.mir.basic_blocks().indices() {
            let i_state = (&in_state[&bb]).clone();
            self.current_environment = i_state;
            self.visit_basic_block(bb);
        }

        // Now create a summary of the body that can be in-lined into call sites.
        let summary = summaries::summarize(
            &self.exit_environment,
            &self.inferred_preconditions,
            &self.path_conditions,
            &self.preconditions,
            &self.post_conditions,
            &self.unwind_condition,
        );
        self.summary_cache.set_summary_for(self.def_id, summary);
    }

    /// Visits each statement in order and then visits the terminator.
    fn visit_basic_block(&mut self, bb: mir::BasicBlock) {
        debug!("visit_basic_block({:?})", bb);

        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.mir[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index]);
            location.statement_index += 1;
        }

        if let Some(mir::Terminator {
            ref source_info,
            ref kind,
        }) = *terminator
        {
            self.visit_terminator(*source_info, kind);
        }
    }

    /// Calls a specialized visitor for each kind of statement.
    fn visit_statement(&mut self, _location: mir::Location, statement: &mir::Statement) {
        let mir::Statement { kind, source_info } = statement;
        debug!("{:?}", source_info);
        self.current_span = source_info.span;
        match kind {
            mir::StatementKind::Assign(place, rvalue) => self.visit_assign(place, rvalue.borrow()),
            mir::StatementKind::FakeRead(..) => unreachable!(),
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => self.visit_set_discriminant(place, *variant_index),
            mir::StatementKind::StorageLive(local) => self.visit_storage_live(*local),
            mir::StatementKind::StorageDead(local) => self.visit_storage_dead(*local),
            mir::StatementKind::InlineAsm {
                asm,
                outputs,
                inputs,
            } => self.visit_inline_asm(asm, outputs, inputs),
            mir::StatementKind::Retag(retag_kind, place) => self.visit_retag(*retag_kind, place),
            mir::StatementKind::AscribeUserType(..) => unreachable!(),
            mir::StatementKind::Nop => return,
        }
    }

    /// Write the RHS Rvalue to the LHS Place.
    fn visit_assign(&mut self, place: &mir::Place, rvalue: &mir::Rvalue) {
        debug!(
            "default visit_assign(place: {:?}, rvalue: {:?})",
            place, rvalue
        );
        let path = self.visit_place(place);
        let rvalue = self.visit_rvalue(rvalue);
        self.current_environment.update_value_at(path, rvalue);
    }

    /// Write the discriminant for a variant to the enum Place.
    fn visit_set_discriminant(
        &self,
        place: &mir::Place,
        variant_index: rustc::ty::layout::VariantIdx,
    ) {
        debug!(
            "default visit_set_discriminant(place: {:?}, variant_index: {:?})",
            place, variant_index
        );
    }

    /// Start a live range for the storage of the local.
    fn visit_storage_live(&self, local: mir::Local) {
        debug!("default visit_storage_live(local: {:?})", local);
    }

    /// End the current live range for the storage of the local.
    fn visit_storage_dead(&self, local: mir::Local) {
        debug!("default visit_storage_dead(local: {:?})", local);
    }

    /// Execute a piece of inline Assembly.
    fn visit_inline_asm(
        &self,
        asm: &hir::InlineAsm,
        outputs: &[mir::Place],
        inputs: &[(syntax_pos::Span, mir::Operand)],
    ) {
        debug!(
            "default visit_inline_asm(asm: {:?}, outputs: {:?}, inputs: {:?})",
            asm, outputs, inputs
        );
    }

    /// Retag references in the given place, ensuring they got fresh tags.  This is
    /// part of the Stacked Borrows model. These statements are currently only interpreted
    /// by miri and only generated when "-Z mir-emit-retag" is passed.
    /// See <https://internals.rust-lang.org/t/stacked-borrows-an-aliasing-model-for-rust/8153/>
    /// for more details.
    fn visit_retag(&self, retag_kind: mir::RetagKind, place: &mir::Place) {
        debug!(
            "default visit_retag(retag_kind: {:?}, place: {:?})",
            retag_kind, place
        );
    }

    /// Calls a specialized visitor for each kind of terminator.
    fn visit_terminator(&mut self, source_info: mir::SourceInfo, kind: &mir::TerminatorKind) {
        debug!("{:?}", source_info);
        self.current_span = source_info.span;
        match kind {
            mir::TerminatorKind::Goto { target } => self.visit_goto(*target),
            mir::TerminatorKind::SwitchInt {
                discr,
                switch_ty,
                values,
                targets,
            } => self.visit_switch_int(discr, switch_ty, values, targets),
            mir::TerminatorKind::Resume => self.visit_resume(),
            mir::TerminatorKind::Abort => self.visit_abort(),
            mir::TerminatorKind::Return => self.visit_return(),
            mir::TerminatorKind::Unreachable => self.visit_unreachable(),
            mir::TerminatorKind::Drop {
                location,
                target,
                unwind,
            } => self.visit_drop(location, *target, *unwind),
            mir::TerminatorKind::DropAndReplace { .. } => unreachable!(),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                cleanup,
                from_hir_call,
            } => self.visit_call(func, args, destination, *cleanup, *from_hir_call),
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                cleanup,
            } => self.visit_assert(cond, *expected, msg, *target, *cleanup),
            mir::TerminatorKind::Yield { .. } => unreachable!(),
            mir::TerminatorKind::GeneratorDrop => unreachable!(),
            mir::TerminatorKind::FalseEdges { .. } => unreachable!(),
            mir::TerminatorKind::FalseUnwind { .. } => unreachable!(),
        }
    }

    /// block should have one successor in the graph; we jump there
    fn visit_goto(&self, target: mir::BasicBlock) {
        debug!("default visit_goto(local: {:?})", target);
    }

    /// `discr` evaluates to an integer; jump depending on its value
    /// to one of the targets, and otherwise fallback to last element of `targets`.
    ///
    /// # Arguments
    /// * `discr` - Discriminant value being tested
    /// * `switch_ty` - type of value being tested
    /// * `values` - Possible values. The locations to branch to in each case
    /// are found in the corresponding indices from the `targets` vector.
    /// * `targets` - Possible branch sites. The last element of this vector is used
    /// for the otherwise branch, so targets.len() == values.len() + 1 should hold.
    fn visit_switch_int(
        &self,
        discr: &mir::Operand,
        switch_ty: rustc::ty::Ty,
        values: &[u128],
        targets: &[mir::BasicBlock],
    ) {
        debug!(
            "default visit_switch_int(discr: {:?}, switch_ty: {:?}, values: {:?}, targets: {:?})",
            discr, switch_ty, values, targets
        );
    }

    /// Indicates that the landing pad is finished and unwinding should
    /// continue. Emitted by build::scope::diverge_cleanup.
    fn visit_resume(&self) {
        debug!("default visit_resume()");
    }

    /// Indicates that the landing pad is finished and that the process
    /// should abort. Used to prevent unwinding for foreign items.
    fn visit_abort(&self) {
        debug!("default visit_abort()");
    }

    /// Indicates a normal return. The return place should have
    /// been filled in by now. This should occur at most once.
    fn visit_return(&self) {
        debug!("default visit_return()");
    }

    /// Indicates a terminator that can never be reached.
    fn visit_unreachable(&self) {
        debug!("default visit_unreachable()");
    }

    /// Drop the Place
    fn visit_drop(
        &self,
        location: &mir::Place,
        target: mir::BasicBlock,
        unwind: Option<mir::BasicBlock>,
    ) {
        debug!(
            "default visit_drop(location: {:?}, target: {:?}, unwind: {:?})",
            location, target, unwind
        );
    }

    /// Block ends with a call of a converging function
    ///
    /// #Arguments
    /// * `func` - The function that’s being called
    /// * `args` - Arguments the function is called with.
    /// These are owned by the callee, which is free to modify them.
    /// This allows the memory occupied by "by-value" arguments to be
    /// reused across function calls without duplicating the contents.
    /// * `destination` - Destination for the return value. If some, the call is converging.
    /// * `cleanup` - Cleanups to be done if the call unwinds.
    /// * `from_hir_call` - Whether this is from a call in HIR, rather than from an overloaded
    /// operator. True for overloaded function call.
    fn visit_call(
        &mut self,
        func: &mir::Operand,
        args: &[mir::Operand],
        destination: &Option<(mir::Place, mir::BasicBlock)>,
        cleanup: Option<mir::BasicBlock>,
        from_hir_call: bool,
    ) {
        debug!("default visit_call(func: {:?}, args: {:?}, destination: {:?}, cleanup: {:?}, from_hir_call: {:?})", func, args, destination, cleanup, from_hir_call);
        let func_to_call = self.visit_operand(func);
        if !self.check_for_errors {
            return;
        }
        if let ExpressionDomain::CompileTimeConstant(fun) = func_to_call.value.expression_domain {
            if self
                .constant_value_cache
                .check_if_std_intrinsics_unreachable_function(&fun)
            {
                let span = self.current_span;
                let mut err = self.session.struct_span_warn(
                    span,
                    "Control might reach a call to std::intrinsics::unreachable",
                );
                (self.emit_diagnostic)(&mut err, &mut self.buffered_diagnostics);
            }
        }
    }

    /// Jump to the target if the condition has the expected value,
    /// otherwise panic with a message and a cleanup target.
    fn visit_assert(
        &self,
        cond: &mir::Operand,
        expected: bool,
        msg: &mir::AssertMessage,
        target: mir::BasicBlock,
        cleanup: Option<mir::BasicBlock>,
    ) {
        debug!("default visit_assert(cond: {:?}, expected: {:?}, msg: {:?}, target: {:?}, cleanup: {:?})", cond, expected, msg, target, cleanup);
    }

    /// Calls a specialized visitor for each kind of Rvalue
    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue) -> AbstractValue {
        match rvalue {
            mir::Rvalue::Use(operand) => self.visit_use(operand),
            mir::Rvalue::Repeat(operand, count) => self.visit_repeat(operand, *count),
            mir::Rvalue::Ref(region, borrow_kind, place) => {
                self.visit_ref(region, *borrow_kind, place)
            }
            mir::Rvalue::Len(place) => self.visit_len(place),
            mir::Rvalue::Cast(cast_kind, operand, ty) => self.visit_cast(*cast_kind, operand, ty),
            mir::Rvalue::BinaryOp(bin_op, left_operand, right_operand) => {
                self.visit_binary_op(*bin_op, left_operand, right_operand)
            }
            mir::Rvalue::CheckedBinaryOp(bin_op, left_operand, right_operand) => {
                self.visit_checked_binary_op(*bin_op, left_operand, right_operand)
            }
            mir::Rvalue::NullaryOp(null_op, ty) => self.visit_nullary_op(*null_op, ty),
            mir::Rvalue::UnaryOp(unary_op, operand) => self.visit_unary_op(*unary_op, operand),
            mir::Rvalue::Discriminant(place) => self.visit_discriminant(place),
            mir::Rvalue::Aggregate(aggregate_kinds, operands) => {
                self.visit_aggregate(aggregate_kinds, operands)
            }
        }
    }

    /// x (either a move or copy, depending on type of x)
    fn visit_use(&mut self, operand: &mir::Operand) -> AbstractValue {
        debug!("default visit_use(operand: {:?})", operand);
        self.visit_operand(operand)
    }

    /// [x; 32]
    fn visit_repeat(&mut self, operand: &mir::Operand, count: u64) -> AbstractValue {
        debug!(
            "default visit_repeat(operand: {:?}, count: {:?})",
            operand, count
        );
        self.visit_operand(operand);
        abstract_value::TOP
    }

    /// &x or &mut x
    fn visit_ref(
        &mut self,
        region: rustc::ty::Region,
        borrow_kind: mir::BorrowKind,
        place: &mir::Place,
    ) -> AbstractValue {
        debug!(
            "default visit_ref(region: {:?}, borrow_kind: {:?}, place: {:?})",
            region, borrow_kind, place
        );
        let path = self.visit_place(place);
        self.lookup_path_and_refine_result(path)
    }

    /// length of a [X] or [X;n] value.
    fn visit_len(&self, place: &mir::Place) -> AbstractValue {
        debug!("default visit_len(place: {:?})", place);
        abstract_value::TOP
    }

    /// cast converts the operand to the given ty.
    fn visit_cast(
        &mut self,
        cast_kind: mir::CastKind,
        operand: &mir::Operand,
        ty: rustc::ty::Ty,
    ) -> AbstractValue {
        debug!(
            "default visit_cast(cast_kind: {:?}, operand: {:?}, ty: {:?})",
            cast_kind, operand, ty
        );
        self.visit_operand(operand)
    }

    /// Apply the given binary operator to the two operands.
    fn visit_binary_op(
        &mut self,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand,
        right_operand: &mir::Operand,
    ) -> AbstractValue {
        debug!(
            "default visit_binary_op(bin_op: {:?}, left_operand: {:?}, right_operand: {:?})",
            bin_op, left_operand, right_operand
        );
        self.visit_operand(left_operand);
        self.visit_operand(right_operand);
        abstract_value::TOP
    }

    /// Apply the given binary operator to the two operands, with overflow checking where appropriate.
    fn visit_checked_binary_op(
        &mut self,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand,
        right_operand: &mir::Operand,
    ) -> AbstractValue {
        debug!("default visit_checked_binary_op(bin_op: {:?}, left_operand: {:?}, right_operand: {:?})", bin_op, left_operand, right_operand);
        self.visit_operand(left_operand);
        self.visit_operand(right_operand);
        abstract_value::TOP
    }

    /// Create a value based on the given type.
    fn visit_nullary_op(&self, null_op: mir::NullOp, ty: rustc::ty::Ty) -> AbstractValue {
        debug!(
            "default visit_nullary_op(null_op: {:?}, ty: {:?})",
            null_op, ty
        );
        abstract_value::TOP
    }

    /// Apply the given unary operator to the operand.
    fn visit_unary_op(&mut self, un_op: mir::UnOp, operand: &mir::Operand) -> AbstractValue {
        debug!(
            "default visit_unary_op(un_op: {:?}, operand: {:?})",
            un_op, operand
        );
        self.visit_operand(operand);
        abstract_value::TOP
    }

    /// Read the discriminant of an ADT.
    ///
    /// Undefined (i.e. no effort is made to make it defined, but there’s no reason why it cannot
    /// be defined to return, say, a 0) if ADT is not an enum.
    fn visit_discriminant(&self, place: &mir::Place) -> AbstractValue {
        debug!("default visit_discriminant(place: {:?})", place);
        abstract_value::TOP
    }

    /// Create an aggregate value, like a tuple or struct.  This is
    /// only needed because we want to distinguish `dest = Foo { x:
    /// ..., y: ... }` from `dest.x = ...; dest.y = ...;` in the case
    /// that `Foo` has a destructor. These rvalues can be optimized
    /// away after type-checking and before lowering.
    fn visit_aggregate(
        &self,
        aggregate_kinds: &mir::AggregateKind,
        operands: &[mir::Operand],
    ) -> AbstractValue {
        debug!(
            "default visit_aggregate(aggregate_kinds: {:?}, operands: {:?})",
            aggregate_kinds, operands
        );
        abstract_value::TOP
    }

    /// These are values that can appear inside an rvalue. They are intentionally
    /// limited to prevent rvalues from being nested in one another.
    fn visit_operand(&mut self, operand: &mir::Operand) -> AbstractValue {
        let span = self.current_span;
        let (expression_domain, span) = match operand {
            mir::Operand::Copy(place) => {
                self.visit_copy(place);
                (ExpressionDomain::Top, span)
            }
            mir::Operand::Move(place) => {
                self.visit_move(place);
                (ExpressionDomain::Top, span)
            }
            mir::Operand::Constant(constant) => {
                let mir::Constant {
                    span,
                    ty,
                    user_ty,
                    literal,
                } = constant.borrow();
                let const_value = self.visit_constant(ty, *user_ty, literal).clone();
                (ExpressionDomain::CompileTimeConstant(const_value), *span)
            }
        };
        AbstractValue {
            provenance: vec![span],
            value: AbstractDomains { expression_domain },
        }
    }

    /// Copy: The value must be available for use afterwards.
    ///
    /// This implies that the type of the place must be `Copy`; this is true
    /// by construction during build, but also checked by the MIR type checker.
    fn visit_copy(&self, place: &mir::Place) {
        debug!("default visit_copy(place: {:?})", place);
    }

    /// Move: The value (including old borrows of it) will not be used again.
    ///
    /// Safe for values of all types (modulo future developments towards `?Move`).
    /// Correct usage patterns are enforced by the borrow checker for safe code.
    /// `Copy` may be converted to `Move` to enable "last-use" optimizations.
    fn visit_move(&mut self, place: &mir::Place) {
        debug!("default visit_move(place: {:?})", place);
        self.visit_place(place);
    }

    /// Synthesizes a constant value.
    fn visit_constant(
        &mut self,
        ty: Ty,
        user_ty: Option<UserTypeAnnotationIndex>,
        literal: &LazyConst,
    ) -> &ConstantValue {
        debug!(
            "default visit_constant(ty: {:?}, user_ty: {:?}, literal: {:?})",
            ty, user_ty, literal
        );
        match ty.sty {
            TyKind::FnDef(def_id, ..) => self.visit_function_reference(def_id),
            _ => &ConstantValue::Unimplemented,
        }
    }

    /// The anonymous type of a function declaration/definition. Each
    /// function has a unique type, which is output (for a function
    /// named `foo` returning an `i32`) as `fn() -> i32 {foo}`.
    ///
    /// For example the type of `bar` here:
    ///
    /// ```rust
    /// fn foo() -> i32 { 1 }
    /// let bar = foo; // bar: fn() -> i32 {foo}
    /// ```
    fn visit_function_reference(&mut self, def_id: hir::def_id::DefId) -> &ConstantValue {
        &mut self.constant_value_cache.get_function_constant_for(
            def_id,
            &self.tcx,
            &mut self.summary_cache,
        )
    }

    /// Returns a Path instance that is the essentially the same as the Place instance, but which
    /// can be serialized and used as a cache key.
    fn visit_place(&mut self, place: &mir::Place) -> Path {
        debug!("default visit_place(place: {:?})", place);
        match place {
            mir::Place::Local(local) => Path::LocalVariable {
                ordinal: local.as_usize(),
            },
            mir::Place::Static(boxed_static) => {
                let def_id = boxed_static.def_id;
                let name = summaries::summary_key_str(&self.tcx, def_id);
                Path::StaticVariable { name }
            }
            mir::Place::Promoted(boxed_promoted) => {
                let index = boxed_promoted.0;
                Path::PromotedConstant {
                    ordinal: index.as_usize(),
                }
            }
            mir::Place::Projection(boxed_place_projection) => {
                let base = self.visit_place(&boxed_place_projection.base);
                let selector = self.visit_projection_elem(&boxed_place_projection.elem);
                Path::QualifiedPath {
                    qualifier: box base,
                    selector: box selector,
                }
            }
        }
    }

    /// Returns a PathSelector instance that is essentially the same as the ProjectionElem instance
    /// but which can be serialized.
    fn visit_projection_elem(
        &mut self,
        projection_elem: &mir::ProjectionElem<mir::Local, &rustc::ty::TyS>,
    ) -> PathSelector {
        debug!(
            "visit_projection_elem(projection_elem: {:?})",
            projection_elem
        );
        match projection_elem {
            mir::ProjectionElem::Deref => PathSelector::Deref,
            mir::ProjectionElem::Field(field, _) => PathSelector::Field(field.index()),
            mir::ProjectionElem::Index(local) => PathSelector::Index(local.as_usize()),
            mir::ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => PathSelector::ConstantIndex {
                offset: *offset,
                min_length: *min_length,
                from_end: *from_end,
            },
            mir::ProjectionElem::Subslice { from, to } => PathSelector::Subslice {
                from: *from,
                to: *to,
            },
            mir::ProjectionElem::Downcast(_, index) => PathSelector::Downcast(index.as_usize()),
        }
    }
}
