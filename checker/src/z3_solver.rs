// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use crate::abstract_value::AbstractValue;
use crate::abstract_value::AbstractValueTrait;
use crate::constant_domain::ConstantDomain;
use crate::expression::{Expression, ExpressionType};
use crate::path::Path;
use crate::smt_solver::SmtResult;
use crate::smt_solver::SmtSolver;
use crate::tag_domain::Tag;

use lazy_static::lazy_static;
use log::debug;
use log_derive::*;
use mirai_annotations::*;
use std::convert::TryFrom;
use std::ffi::{CStr, CString};
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;
use std::sync::Mutex;

pub type Z3ExpressionType = z3_sys::Z3_ast;

lazy_static! {
    static ref Z3_MUTEX: Mutex<()> = Mutex::new(());
}

pub struct Z3Solver {
    z3_context: z3_sys::Z3_context,
    z3_solver: z3_sys::Z3_solver,
    any_sort: z3_sys::Z3_sort,
    bool_sort: z3_sys::Z3_sort,
    int_sort: z3_sys::Z3_sort,
    f32_sort: z3_sys::Z3_sort,
    f64_sort: z3_sys::Z3_sort,
    nearest_even: z3_sys::Z3_ast,
    zero: z3_sys::Z3_ast,
    one: z3_sys::Z3_ast,
    two: z3_sys::Z3_ast,
    empty_str: z3_sys::Z3_string,
    /// A logical predicate has_tag(path, tag) that indicates path is attached with tag.
    has_tag_func: z3_sys::Z3_func_decl,
}

impl Debug for Z3Solver {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "Z3Solver".fmt(f)
    }
}

impl Z3Solver {
    #[logfn_inputs(TRACE)]
    pub fn new() -> Z3Solver {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            let z3_sys_cfg = z3_sys::Z3_mk_config();
            let time_out = CString::new("timeout").unwrap().into_raw();
            let ms = CString::new("100").unwrap().into_raw();
            z3_sys::Z3_set_param_value(z3_sys_cfg, time_out, ms);

            let z3_context = z3_sys::Z3_mk_context(z3_sys_cfg);
            let z3_solver = z3_sys::Z3_mk_solver(z3_context);
            let empty_str = CString::new("").unwrap().into_raw();
            let symbol = z3_sys::Z3_mk_string_symbol(z3_context, empty_str);

            let any_sort = z3_sys::Z3_mk_uninterpreted_sort(z3_context, symbol);
            let bool_sort = z3_sys::Z3_mk_bool_sort(z3_context);
            let int_sort = z3_sys::Z3_mk_int_sort(z3_context);
            let f32_sort = z3_sys::Z3_mk_fpa_sort_32(z3_context);
            let f64_sort = z3_sys::Z3_mk_fpa_sort_64(z3_context);
            let nearest_even = z3_sys::Z3_mk_fpa_round_nearest_ties_to_even(z3_context);
            let zero = z3_sys::Z3_mk_int(z3_context, 0, int_sort);
            let one = z3_sys::Z3_mk_int(z3_context, 1, int_sort);
            let two = z3_sys::Z3_mk_int(z3_context, 2, int_sort);

            let has_tag_func = z3_sys::Z3_mk_func_decl(
                z3_context,
                z3_sys::Z3_mk_string_symbol(
                    z3_context,
                    CString::new("has_tag").unwrap().into_raw(),
                ),
                2,
                [any_sort, any_sort].as_ptr(),
                bool_sort,
            );

            Z3Solver {
                z3_context,
                z3_solver,
                any_sort,
                bool_sort,
                int_sort,
                f32_sort,
                f64_sort,
                nearest_even,
                zero,
                one,
                two,
                empty_str,
                has_tag_func,
            }
        }
    }
}

impl Default for Z3Solver {
    #[logfn_inputs(TRACE)]
    fn default() -> Self {
        Z3Solver::new()
    }
}

impl SmtSolver<Z3ExpressionType> for Z3Solver {
    #[logfn_inputs(TRACE)]
    fn as_debug_string(&self, expression: &Z3ExpressionType) -> String {
        let _guard = Z3_MUTEX.lock().unwrap();
        self.as_debug_string_helper(*expression)
    }

    #[logfn_inputs(TRACE)]
    fn assert(&self, expression: &Z3ExpressionType) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            z3_sys::Z3_solver_assert(self.z3_context, self.z3_solver, *expression);
        }
    }

    #[logfn_inputs(TRACE)]
    fn backtrack(&self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            z3_sys::Z3_solver_pop(self.z3_context, self.z3_solver, 1);
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_as_smt_predicate(&self, mirai_expression: &Expression) -> Z3ExpressionType {
        let _guard = Z3_MUTEX.lock().unwrap();
        self.get_as_bool_z3_ast(mirai_expression)
    }

    #[logfn_inputs(TRACE)]
    fn get_model_as_string(&self) -> String {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            let model = z3_sys::Z3_solver_get_model(self.z3_context, self.z3_solver);
            let debug_str_bytes = z3_sys::Z3_model_to_string(self.z3_context, model);
            let debug_str = CStr::from_ptr(debug_str_bytes);
            debug_str.to_str().unwrap().to_string()
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_solver_state_as_string(&self) -> String {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            let debug_str_bytes = z3_sys::Z3_solver_to_string(self.z3_context, self.z3_solver);
            let debug_str = CStr::from_ptr(debug_str_bytes);
            debug_str.to_str().unwrap().to_string()
        }
    }

    #[logfn_inputs(TRACE)]
    fn invert_predicate(&self, expression: &Z3ExpressionType) -> Z3ExpressionType {
        unsafe { z3_sys::Z3_mk_not(self.z3_context, *expression) }
    }

    #[logfn_inputs(TRACE)]
    fn set_backtrack_position(&self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            z3_sys::Z3_solver_push(self.z3_context, self.z3_solver);
        }
    }

    #[logfn_inputs(TRACE)]
    fn solve(&self) -> SmtResult {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            match z3_sys::Z3_solver_check(self.z3_context, self.z3_solver) {
                z3_sys::Z3_L_TRUE => SmtResult::Satisfiable,
                z3_sys::Z3_L_FALSE => SmtResult::Unsatisfiable,
                _ => SmtResult::Undefined,
            }
        }
    }
}

impl Z3Solver {
    fn as_debug_string_helper(&self, expression: Z3ExpressionType) -> String {
        unsafe {
            let debug_str_bytes = z3_sys::Z3_ast_to_string(self.z3_context, expression);
            let debug_str = CStr::from_ptr(debug_str_bytes);
            String::from(debug_str.to_str().unwrap())
        }
    }

    #[logfn_inputs(TRACE)]
    fn boolean_join(&self, left: &Rc<AbstractValue>, right: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        let left_ast = self.get_as_bool_z3_ast(&left.expression);
        let right_ast = self.get_as_bool_z3_ast(&right.expression);
        unsafe {
            let sym = self.get_symbol_for(self);
            let condition_ast = z3_sys::Z3_mk_const(self.z3_context, sym, self.bool_sort);
            z3_sys::Z3_mk_ite(self.z3_context, condition_ast, left_ast, right_ast)
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_as_z3_ast(&self, expression: &Expression) -> z3_sys::Z3_ast {
        match expression {
            Expression::HeapBlock { .. } => {
                let path = Path::get_as_path(AbstractValue::make_from(expression.clone(), 1));
                self.general_variable(&path, expression.infer_type())
            }
            Expression::Add { .. }
            | Expression::AddOverflows { .. }
            | Expression::Div { .. }
            | Expression::IntrinsicBinary { .. }
            | Expression::IntrinsicFloatingPointUnary { .. }
            | Expression::Mul { .. }
            | Expression::MulOverflows { .. }
            | Expression::Rem { .. }
            | Expression::Sub { .. }
            | Expression::SubOverflows { .. } => self.get_as_numeric_z3_ast(expression).1,
            Expression::And { left, right } => {
                self.general_boolean_op(left, right, z3_sys::Z3_mk_and)
            }
            Expression::BitAnd { left, right } => {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) = left.expression {
                    if v < u128::MAX && (v + 1).is_power_of_two() {
                        let p2: Rc<AbstractValue> = Rc::new((v + 1).into());
                        return self.numeric_rem(right, &p2).1;
                    }
                }
                self.get_as_bv_z3_ast(expression, 128)
            }
            Expression::BitOr { .. } | Expression::BitXor { .. } => {
                self.get_as_bv_z3_ast(expression, 128)
            }
            Expression::BitNot { result_type, .. } => {
                self.get_as_bv_z3_ast(expression, u32::from(result_type.bit_length()))
            }
            Expression::Cast {
                operand,
                target_type,
            } => self.general_cast(operand, *target_type),
            Expression::CompileTimeConstant(const_domain) => self.get_constant_as_ast(const_domain),
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => self.general_conditional(condition, consequent, alternate),
            Expression::Equals { left, right } => self.general_relational(
                left,
                right,
                z3_sys::Z3_mk_fpa_eq,
                z3_sys::Z3_mk_eq,
                z3_sys::Z3_mk_eq,
                z3_sys::Z3_mk_eq,
            ),
            Expression::GreaterOrEqual { left, right } => self.general_relational(
                left,
                right,
                z3_sys::Z3_mk_fpa_geq,
                z3_sys::Z3_mk_ge,
                z3_sys::Z3_mk_bvsge,
                z3_sys::Z3_mk_bvuge,
            ),
            Expression::GreaterThan { left, right } => self.general_relational(
                left,
                right,
                z3_sys::Z3_mk_fpa_gt,
                z3_sys::Z3_mk_gt,
                z3_sys::Z3_mk_bvsgt,
                z3_sys::Z3_mk_bvugt,
            ),
            Expression::InitialParameterValue { path, .. }
            | Expression::UninterpretedCall { path, .. }
            | Expression::UnknownModelField { path, .. }
            | Expression::UnknownTagField { path }
            | Expression::Variable { path, .. } => {
                self.general_variable(path, expression.infer_type())
            }
            Expression::IntrinsicBitVectorUnary { bit_length, .. } => {
                self.get_as_bv_z3_ast(expression, u32::from(*bit_length))
            }
            Expression::LessOrEqual { left, right } => self.general_relational(
                left,
                right,
                z3_sys::Z3_mk_fpa_leq,
                z3_sys::Z3_mk_le,
                z3_sys::Z3_mk_bvsle,
                z3_sys::Z3_mk_bvule,
            ),
            Expression::LessThan { left, right } => self.general_relational(
                left,
                right,
                z3_sys::Z3_mk_fpa_lt,
                z3_sys::Z3_mk_lt,
                z3_sys::Z3_mk_bvslt,
                z3_sys::Z3_mk_bvult,
            ),
            Expression::LogicalNot { operand } => self.general_logical_not(operand),
            Expression::Ne { left, right } => self.general_ne(left, right),
            Expression::Neg { operand } => self.general_negation(operand),
            Expression::Offset { .. } => unsafe {
                let sort = self.get_sort_for(expression.infer_type());
                let sym = self.get_symbol_for(expression);
                z3_sys::Z3_mk_const(self.z3_context, sym, sort)
            },
            Expression::Or { left, right } => {
                self.general_boolean_op(left, right, z3_sys::Z3_mk_or)
            }
            Expression::Reference(path) => self.general_reference(path),
            Expression::Shl { left, right } => {
                self.bv_binary(128, left, right, z3_sys::Z3_mk_bvshl)
            }
            Expression::Shr { left, right } => self.general_shr(left, right),
            Expression::ShlOverflows {
                right, result_type, ..
            }
            | Expression::ShrOverflows {
                right, result_type, ..
            } => self.general_shift_overflows(right, *result_type),
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => self.general_switch(discriminator, cases, default, |e| self.get_as_z3_ast(e)),
            Expression::TaggedExpression { operand, .. } => self.get_as_z3_ast(&operand.expression),
            Expression::Top | Expression::Bottom => unsafe {
                z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.any_sort)
            },
            Expression::UnknownTagCheck {
                operand,
                tag,
                checking_presence,
            } => {
                let check_ast = self.general_has_tag(&operand.expression, tag);
                if *checking_presence {
                    check_ast
                } else {
                    unsafe { z3_sys::Z3_mk_not(self.z3_context, check_ast) }
                }
            }
            Expression::WidenedJoin { path, operand } => {
                self.get_ast_for_widened(path, operand, operand.expression.infer_type())
            }
            Expression::Join { left, right, .. } => self.general_join(left, right),
            _ => unsafe {
                debug!("uninterpreted expression: {:?}", expression);
                let sym = self.get_symbol_for(expression);
                let sort = self.get_sort_for(expression.infer_type());
                z3_sys::Z3_mk_const(self.z3_context, sym, sort)
            },
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_boolean_op(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        operation: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            num_args: std::os::raw::c_uint,
            args: *const z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> z3_sys::Z3_ast {
        let left_ast = self.get_as_bool_z3_ast(&left.expression);
        let right_ast = self.get_as_bool_z3_ast(&right.expression);
        unsafe {
            let tmp = vec![left_ast, right_ast];
            operation(self.z3_context, 2, tmp.as_ptr())
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_cast(
        &self,
        operand: &Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> z3_sys::Z3_ast {
        if target_type == ExpressionType::NonPrimitive || target_type == ExpressionType::ThinPointer
        {
            self.get_as_z3_ast(&operand.expression)
        } else if target_type == ExpressionType::Bool {
            self.get_as_bool_z3_ast(&operand.expression)
        } else {
            self.get_as_numeric_z3_ast(&operand.expression).1
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_conditional(
        &self,
        condition: &Rc<AbstractValue>,
        consequent: &Rc<AbstractValue>,
        alternate: &Rc<AbstractValue>,
    ) -> z3_sys::Z3_ast {
        let condition_ast = self.get_as_bool_z3_ast(&condition.expression);
        let consequent_ast = self.get_as_z3_ast(&consequent.expression);
        let alternate_ast = self.get_as_z3_ast(&alternate.expression);
        unsafe {
            z3_sys::Z3_mk_ite(
                self.z3_context,
                condition_ast,
                consequent_ast,
                alternate_ast,
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_relational(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        float_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
        int_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
        signed_bit_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
        unsigned_bit_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> z3_sys::Z3_ast {
        let (signed, num_bits) = if left.expression.is_bit_vector() {
            let ty = left.expression.infer_type();
            (ty.is_signed_integer(), u32::from(ty.bit_length()))
        } else if right.expression.is_bit_vector() {
            let ty = right.expression.infer_type();
            let mut result = (ty.is_signed_integer(), u32::from(ty.bit_length()));
            if let Expression::BitAnd { left, .. } = &right.expression {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) = left.expression {
                    if v < u128::MAX && (v + 1).is_power_of_two() {
                        result = (false, 0);
                    }
                }
            }
            result
        } else {
            (false, 0)
        };
        if num_bits > 0 {
            let left_ast = self.get_as_bv_z3_ast(&left.expression, num_bits);
            let right_ast = self.get_as_bv_z3_ast(&right.expression, num_bits);
            unsafe {
                if signed {
                    signed_bit_op(self.z3_context, left_ast, right_ast)
                } else {
                    unsigned_bit_op(self.z3_context, left_ast, right_ast)
                }
            }
        } else {
            let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
            let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
            if lf != rf {
                warn!("can't encode {:?} relational op {:?}", left, right);
                return self
                    .general_variable(&Path::get_as_path(left.clone()), ExpressionType::Bool);
            }
            unsafe {
                if lf {
                    float_op(self.z3_context, left_ast, right_ast)
                } else {
                    int_op(self.z3_context, left_ast, right_ast)
                }
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_ne(&self, left: &Rc<AbstractValue>, right: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        let num_bits = if left.expression.is_bit_vector() {
            u32::from(left.expression.infer_type().bit_length())
        } else if right.expression.is_bit_vector() {
            let mut result = u32::from(right.expression.infer_type().bit_length());
            if let Expression::BitAnd { left, .. } = &right.expression {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) = left.expression {
                    if v < u128::MAX && (v + 1).is_power_of_two() {
                        result = 0;
                    }
                }
            }
            result
        } else {
            0
        };
        if num_bits > 0 {
            let left_ast = self.get_as_bv_z3_ast(&left.expression, num_bits);
            let right_ast = self.get_as_bv_z3_ast(&right.expression, num_bits);
            unsafe {
                z3_sys::Z3_mk_not(
                    self.z3_context,
                    z3_sys::Z3_mk_eq(self.z3_context, left_ast, right_ast),
                )
            }
        } else {
            let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
            let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
            if lf != rf {
                warn!("can't encode {:?} != {:?}", left, right);
                return self
                    .general_variable(&Path::get_as_path(left.clone()), ExpressionType::Bool);
            }
            unsafe {
                if lf {
                    let l = z3_sys::Z3_mk_fpa_is_nan(self.z3_context, left_ast);
                    let r = z3_sys::Z3_mk_fpa_is_nan(self.z3_context, right_ast);
                    let eq = z3_sys::Z3_mk_fpa_eq(self.z3_context, left_ast, right_ast);
                    let ne = z3_sys::Z3_mk_not(self.z3_context, eq);
                    let tmp = vec![l, r, ne];
                    z3_sys::Z3_mk_or(self.z3_context, 3, tmp.as_ptr())
                } else {
                    z3_sys::Z3_mk_not(
                        self.z3_context,
                        z3_sys::Z3_mk_eq(self.z3_context, left_ast, right_ast),
                    )
                }
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_negation(&self, operand: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        let (is_float, operand_ast) = self.get_as_numeric_z3_ast(&operand.expression);
        unsafe {
            if is_float {
                z3_sys::Z3_mk_fpa_neg(self.z3_context, operand_ast)
            } else {
                z3_sys::Z3_mk_unary_minus(self.z3_context, operand_ast)
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_logical_not(&self, operand: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        let operand_ast = self.get_as_bool_z3_ast(&operand.expression);
        unsafe { z3_sys::Z3_mk_not(self.z3_context, operand_ast) }
    }

    #[logfn_inputs(TRACE)]
    fn general_reference(&self, path: &Rc<Path>) -> z3_sys::Z3_ast {
        unsafe {
            let path_symbol = self.get_symbol_for(path);
            z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.any_sort)
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_shr(&self, left: &Rc<AbstractValue>, right: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        let result_type = left.expression.infer_type();
        let num_bits = u32::from(result_type.bit_length());
        let left_ast = self.get_as_bv_z3_ast(&left.expression, num_bits);
        let right_ast = self.get_as_bv_z3_ast(&right.expression, num_bits);
        unsafe {
            if result_type.is_signed_integer() {
                z3_sys::Z3_mk_bvashr(self.z3_context, left_ast, right_ast)
            } else {
                z3_sys::Z3_mk_bvlshr(self.z3_context, left_ast, right_ast)
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_shift_overflows(
        &self,
        right: &Rc<AbstractValue>,
        result_type: ExpressionType,
    ) -> z3_sys::Z3_ast {
        let (f, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        checked_assume!(!f);
        let num_bits = i32::from(result_type.bit_length());
        unsafe {
            let num_bits_val = z3_sys::Z3_mk_int(self.z3_context, num_bits, self.int_sort);
            z3_sys::Z3_mk_ge(self.z3_context, right_ast, num_bits_val)
        }
    }

    fn general_switch<F>(
        &self,
        discriminator: &Rc<AbstractValue>,
        cases: &[(Rc<AbstractValue>, Rc<AbstractValue>)],
        default: &Rc<AbstractValue>,
        get_result_ast: F,
    ) -> z3_sys::Z3_ast
    where
        F: FnOnce(&Expression) -> z3_sys::Z3_ast + Copy,
    {
        trace!(
            "general_switch(discriminator {:?}, cases: {:?}, default {:?})",
            discriminator,
            cases,
            default
        );
        if discriminator.expression.is_bit_vector() {
            return self.switch_with_bv_discriminator(
                discriminator,
                cases,
                default,
                get_result_ast,
            );
        }
        let discriminator_type = discriminator.expression.infer_type();
        let discriminator_ast = self.get_as_z3_ast(&discriminator.expression);
        let default_ast = get_result_ast(&default.expression);
        cases
            .iter()
            .fold(default_ast, |acc_ast, (case_val, case_result)| unsafe {
                let case_val_type = case_val.expression.infer_type();
                let case_val_ast = if case_val_type != discriminator_type {
                    debug!(
                        "mismatching discriminator and case_val: {:?} {:?}",
                        discriminator, **case_val
                    );
                    let sym = self.get_symbol_for(&case_val.expression);
                    let sort = self.get_sort_for(discriminator_type);
                    z3_sys::Z3_mk_const(self.z3_context, sym, sort)
                } else {
                    self.get_as_z3_ast(&case_val.expression)
                };
                let cond_ast = z3_sys::Z3_mk_eq(self.z3_context, discriminator_ast, case_val_ast);
                let case_result_ast = get_result_ast(&case_result.expression);
                z3_sys::Z3_mk_ite(self.z3_context, cond_ast, case_result_ast, acc_ast)
            })
    }

    #[logfn_inputs(TRACE)]
    fn general_variable(&self, path: &Rc<Path>, var_type: ExpressionType) -> z3_sys::Z3_ast {
        unsafe {
            let path_symbol = self.get_symbol_for(path);
            let sort = self.get_sort_for(var_type);
            let ast = z3_sys::Z3_mk_const(self.z3_context, path_symbol, sort);
            if var_type.is_integer() {
                let min_ast = self.get_constant_as_ast(&var_type.min_value());
                let max_ast = self.get_constant_as_ast(&var_type.max_value());
                let range_check = self.get_range_check(ast, min_ast, max_ast);

                // Side-effecting the solver smells bad, but it hard to come up with an expression
                // of type var_type that only take values that satisfies the range constraint.
                // Since this is kind of a lazy variable declaration, it is probably OK.

                // It turns out that if there were previous calls to the smt solver that produced strings
                // this call will crash
                z3_sys::Z3_solver_assert(self.z3_context, self.z3_solver, range_check);
            }
            ast
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_join(&self, left: &Rc<AbstractValue>, right: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        if left.expression.is_bit_vector() || right.expression.is_bit_vector() {
            return self.bv_join(left, right, 128);
        }
        let left_ast = self.get_as_z3_ast(&left.expression);
        let right_ast = self.get_as_z3_ast(&right.expression);
        unsafe {
            let sym = self.get_symbol_for(self);
            let condition_ast = z3_sys::Z3_mk_const(self.z3_context, sym, self.bool_sort);
            z3_sys::Z3_mk_ite(self.z3_context, condition_ast, left_ast, right_ast)
        }
    }

    #[logfn_inputs(TRACE)]
    fn general_has_tag(&self, expression: &Expression, tag: &Tag) -> z3_sys::Z3_ast {
        let exp_tag_prop_opt = expression.get_tag_propagation();

        // First deal with expressions that do not propagate tags or have special propagation behavior.
        match expression {
            Expression::Top
            | Expression::Bottom
            | Expression::CompileTimeConstant { .. }
            | Expression::HeapBlock { .. }
            | Expression::HeapBlockLayout { .. }
            | Expression::Reference { .. }
            | Expression::UnknownTagCheck { .. } => unsafe {
                return z3_sys::Z3_mk_false(self.z3_context);
            },

            Expression::InitialParameterValue { path, .. }
            | Expression::UnknownModelField { path, .. }
            | Expression::UnknownTagField { path }
            | Expression::Variable { path, .. } => {
                // A variable is an unknown value of a place in memory.
                // Therefore, returns an unknown tag check via the logical predicate has_tag(path, tag).
                unsafe {
                    let path_symbol = self.get_symbol_for(path);
                    let path_arg = z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.any_sort);
                    let tag_symbol = self.get_symbol_for(tag);
                    let tag_arg = z3_sys::Z3_mk_const(self.z3_context, tag_symbol, self.any_sort);
                    return z3_sys::Z3_mk_app(
                        self.z3_context,
                        self.has_tag_func,
                        2,
                        [path_arg, tag_arg].as_ptr(),
                    );
                }
            }

            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                // Whether the conditional expression has tag or not is computed by
                // (condition has tag) or ite(condition, (consequent has tag), (alternate has tag)).
                let condition_ast = self.get_as_bool_z3_ast(&condition.expression);
                let condition_check = self.general_has_tag(&condition.expression, tag);
                let consequent_check = self.general_has_tag(&consequent.expression, tag);
                let alternate_check = self.general_has_tag(&alternate.expression, tag);
                unsafe {
                    let join_check = z3_sys::Z3_mk_ite(
                        self.z3_context,
                        condition_ast,
                        consequent_check,
                        alternate_check,
                    );
                    return z3_sys::Z3_mk_or(
                        self.z3_context,
                        2,
                        [condition_check, join_check].as_ptr(),
                    );
                }
            }

            Expression::Join { left, right, .. } => {
                // Whether the join expression has tag or not is computed by
                // ite(unknown condition, (left has tag), (right has tag)).
                let left_check = self.general_has_tag(&left.expression, tag);
                let right_check = self.general_has_tag(&right.expression, tag);
                unsafe {
                    let sym = self.get_symbol_for(self);
                    let condition_ast = z3_sys::Z3_mk_const(self.z3_context, sym, self.bool_sort);
                    return z3_sys::Z3_mk_ite(
                        self.z3_context,
                        condition_ast,
                        left_check,
                        right_check,
                    );
                }
            }

            Expression::Switch {
                discriminator,
                cases,
                default,
            } => {
                // Whether the switch expression has tag or not is computed by
                // (discriminator has tag) or (switch (discriminator) { case0 => (case0 has tag) | ... | _ => (default has tag) }).
                let discriminator_ast = self.get_as_z3_ast(&discriminator.expression);
                let discriminator_check = self.general_has_tag(&discriminator.expression, tag);
                let default_check = self.general_has_tag(&default.expression, tag);
                let join_check =
                    cases
                        .iter()
                        .fold(default_check, |acc_check, (case_val, case_result)| unsafe {
                            let case_val_ast = self.get_as_z3_ast(&case_val.expression);
                            let cond_ast =
                                z3_sys::Z3_mk_eq(self.z3_context, discriminator_ast, case_val_ast);
                            let case_result_check =
                                self.general_has_tag(&case_result.expression, tag);
                            z3_sys::Z3_mk_ite(
                                self.z3_context,
                                cond_ast,
                                case_result_check,
                                acc_check,
                            )
                        });
                unsafe {
                    return z3_sys::Z3_mk_or(
                        self.z3_context,
                        2,
                        [discriminator_check, join_check].as_ptr(),
                    );
                }
            }

            Expression::TaggedExpression {
                operand,
                tag: annotated_tag,
            } => {
                if tag.eq(annotated_tag) {
                    unsafe {
                        return z3_sys::Z3_mk_true(self.z3_context);
                    }
                } else {
                    return self.general_has_tag(&operand.expression, tag);
                }
            }

            Expression::WidenedJoin { operand, .. } => {
                return self.general_has_tag(&operand.expression, tag);
            }

            _ => {
                verify!(exp_tag_prop_opt.is_some());
            }
        }

        let exp_tag_prop = exp_tag_prop_opt.unwrap();

        // Then deal with expressions that have standard propagation behavior, i.e., taking tags
        // from children nodes.
        if tag.is_propagated_by(exp_tag_prop) {
            // The operand will propagate the tag.
            match expression {
                Expression::Add { left, right }
                | Expression::AddOverflows { left, right, .. }
                | Expression::And { left, right }
                | Expression::BitAnd { left, right }
                | Expression::BitOr { left, right }
                | Expression::BitXor { left, right }
                | Expression::Div { left, right }
                | Expression::Equals { left, right }
                | Expression::GreaterOrEqual { left, right }
                | Expression::GreaterThan { left, right }
                | Expression::IntrinsicBinary { left, right, .. }
                | Expression::LessOrEqual { left, right }
                | Expression::LessThan { left, right }
                | Expression::Mul { left, right }
                | Expression::MulOverflows { left, right, .. }
                | Expression::Ne { left, right }
                | Expression::Or { left, right }
                | Expression::Offset { left, right }
                | Expression::Rem { left, right }
                | Expression::Shl { left, right }
                | Expression::ShlOverflows { left, right, .. }
                | Expression::Shr { left, right, .. }
                | Expression::ShrOverflows { left, right, .. }
                | Expression::Sub { left, right }
                | Expression::SubOverflows { left, right, .. } => {
                    let left_check = self.general_has_tag(&left.expression, tag);
                    let right_check = self.general_has_tag(&right.expression, tag);
                    unsafe {
                        z3_sys::Z3_mk_or(self.z3_context, 2, [left_check, right_check].as_ptr())
                    }
                }

                Expression::BitNot { operand, .. }
                | Expression::Cast { operand, .. }
                | Expression::IntrinsicBitVectorUnary { operand, .. }
                | Expression::IntrinsicFloatingPointUnary { operand, .. }
                | Expression::LogicalNot { operand, .. }
                | Expression::Neg { operand, .. }
                | Expression::Transmute { operand, .. } => {
                    self.general_has_tag(&operand.expression, tag)
                }

                Expression::UninterpretedCall {
                    callee, arguments, ..
                } => {
                    let mut checks = vec![self.general_has_tag(&callee.expression, tag)];
                    for argument in arguments {
                        checks.push(self.general_has_tag(&argument.expression, tag));
                    }
                    unsafe {
                        z3_sys::Z3_mk_or(
                            self.z3_context,
                            u32::try_from(checks.len()).unwrap(),
                            checks.as_ptr(),
                        )
                    }
                }

                _ => {
                    verify_unreachable!();
                }
            }
        } else {
            // Otherwise, the operand does not propagate the tag, so the result is false.
            unsafe { z3_sys::Z3_mk_false(self.z3_context) }
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_symbol_for<T>(&self, value: T) -> z3_sys::Z3_symbol
    where
        T: Debug,
    {
        let sym_str = CString::new(format!("{:?}", value)).unwrap();
        unsafe { z3_sys::Z3_mk_string_symbol(self.z3_context, sym_str.into_raw()) }
    }

    #[logfn_inputs(TRACE)]
    fn get_sort_for(&self, var_type: ExpressionType) -> z3_sys::Z3_sort {
        use self::ExpressionType::*;
        match var_type {
            Bool => self.bool_sort,
            Char | I8 | I16 | I32 | I64 | I128 | Isize | U8 | U16 | U32 | U64 | U128 | Usize => {
                self.int_sort
            }
            F32 => self.f32_sort,
            F64 => self.f64_sort,
            NonPrimitive | ThinPointer | Unit => self.any_sort,
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_ast_for_widened(
        &self,
        path: &Rc<Path>,
        operand: &Rc<AbstractValue>,
        target_type: ExpressionType,
    ) -> z3_sys::Z3_ast {
        let sort = self.get_sort_for(target_type);
        unsafe {
            let path_symbol = self.get_symbol_for(path);
            let ast = z3_sys::Z3_mk_const(self.z3_context, path_symbol, sort);
            if target_type.is_integer() {
                let interval = operand.widen(path).get_as_interval();
                if !interval.is_bottom() {
                    if let Some(lower_bound) = interval.lower_bound() {
                        let lb = self.get_constant_as_ast(&ConstantDomain::I128(lower_bound));
                        let ge_lower_bound = z3_sys::Z3_mk_ge(self.z3_context, ast, lb);
                        // An interval is kind of like a type and the side-effect here is akin to the
                        // one in Expression::Variable. See the comments there for justification.
                        z3_sys::Z3_solver_assert(self.z3_context, self.z3_solver, ge_lower_bound);
                    }
                    if let Some(upper_bound) = interval.upper_bound() {
                        let ub = self.get_constant_as_ast(&ConstantDomain::I128(upper_bound));
                        let le_upper_bound = z3_sys::Z3_mk_le(self.z3_context, ast, ub);
                        // An interval is kind of like a type and the side-effect here is akin to the
                        // one in Expression::Variable. See the comments there for justification.
                        z3_sys::Z3_solver_assert(self.z3_context, self.z3_solver, le_upper_bound);
                    }
                }
            }
            ast
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_constant_as_ast(&self, const_domain: &ConstantDomain) -> z3_sys::Z3_ast {
        match const_domain {
            ConstantDomain::Char(v) => unsafe {
                z3_sys::Z3_mk_int(self.z3_context, i32::from(*v as u16), self.int_sort)
            },
            ConstantDomain::False => unsafe { z3_sys::Z3_mk_false(self.z3_context) },
            ConstantDomain::I128(v) => unsafe {
                let v64 = i64::try_from(*v);
                if let Ok(v64) = v64 {
                    z3_sys::Z3_mk_int64(self.z3_context, v64, self.int_sort)
                } else {
                    let num_str = format!("{}", *v);
                    let c_string = CString::new(num_str).unwrap();
                    z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), self.int_sort)
                }
            },
            ConstantDomain::F32(v) => unsafe {
                let fv = f32::from_bits(*v);
                z3_sys::Z3_mk_fpa_numeral_float(self.z3_context, fv, self.f32_sort)
            },
            ConstantDomain::F64(v) => unsafe {
                let fv = f64::from_bits(*v);
                z3_sys::Z3_mk_fpa_numeral_double(self.z3_context, fv, self.f64_sort)
            },
            ConstantDomain::U128(v) => unsafe {
                let v64 = u64::try_from(*v);
                if let Ok(v64) = v64 {
                    z3_sys::Z3_mk_unsigned_int64(self.z3_context, v64, self.int_sort)
                } else {
                    let num_str = format!("{}", *v);
                    let c_string = CString::new(num_str).unwrap();
                    z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), self.int_sort)
                }
            },
            ConstantDomain::True => unsafe { z3_sys::Z3_mk_true(self.z3_context) },
            _ => unsafe {
                let sym = self.get_symbol_for(const_domain);
                z3_sys::Z3_mk_const(self.z3_context, sym, self.any_sort)
            },
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_range_check(
        &self,
        operand_ast: z3_sys::Z3_ast,
        min_ast: z3_sys::Z3_ast,
        max_ast: z3_sys::Z3_ast,
    ) -> z3_sys::Z3_ast {
        unsafe {
            let min_is_le = z3_sys::Z3_mk_le(self.z3_context, min_ast, operand_ast);
            let max_is_ge = z3_sys::Z3_mk_ge(self.z3_context, max_ast, operand_ast);
            let tmp = vec![min_is_le, max_is_ge];
            z3_sys::Z3_mk_and(self.z3_context, 2, tmp.as_ptr())
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_as_numeric_z3_ast(&self, expression: &Expression) -> (bool, z3_sys::Z3_ast) {
        match expression {
            Expression::HeapBlock { .. } => {
                let path = Path::get_as_path(AbstractValue::make_from(expression.clone(), 1));
                self.numeric_variable(&path, expression.infer_type())
            }
            Expression::Add { left, right } => {
                self.numeric_binary_var_arg(left, right, z3_sys::Z3_mk_fpa_add, z3_sys::Z3_mk_add)
            }
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => self.numeric_binary_overflow_vararg(left, right, *result_type, z3_sys::Z3_mk_add),
            Expression::Div { left, right } => {
                self.numeric_binary(left, right, z3_sys::Z3_mk_fpa_div, z3_sys::Z3_mk_div)
            }
            Expression::Join { left, right, .. } => self.numeric_join(left, right),
            Expression::Mul { left, right } => {
                self.numeric_binary_var_arg(left, right, z3_sys::Z3_mk_fpa_mul, z3_sys::Z3_mk_mul)
            }
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => self.numeric_binary_overflow_vararg(left, right, *result_type, z3_sys::Z3_mk_mul),
            Expression::Rem { left, right } => self.numeric_rem(left, right),
            Expression::Sub { left, right } => {
                self.numeric_binary_var_arg(left, right, z3_sys::Z3_mk_fpa_sub, z3_sys::Z3_mk_sub)
            }
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => self.numeric_binary_overflow_vararg(left, right, *result_type, z3_sys::Z3_mk_sub),
            Expression::And { .. }
            | Expression::Equals { .. }
            | Expression::GreaterOrEqual { .. }
            | Expression::GreaterThan { .. }
            | Expression::LessOrEqual { .. }
            | Expression::LessThan { .. }
            | Expression::LogicalNot { .. }
            | Expression::Ne { .. }
            | Expression::Or { .. } => self.numeric_boolean_op(expression),
            Expression::BitAnd { left, right } => {
                if let Expression::CompileTimeConstant(ConstantDomain::U128(v)) = left.expression {
                    if v < u128::MAX && (v + 1).is_power_of_two() {
                        let p2: Rc<AbstractValue> = Rc::new((v + 1).into());
                        return self.numeric_rem(right, &p2);
                    }
                }
                self.numeric_bitwise_expression(expression)
            }
            Expression::BitOr { .. } | Expression::BitXor { .. } => {
                self.numeric_bitwise_expression(expression)
            }
            Expression::BitNot {
                operand,
                result_type,
            } => self.numeric_bitwise_not(operand, *result_type),
            Expression::Cast {
                operand,
                target_type,
            } => self.numeric_cast(&operand.expression, *target_type),
            Expression::CompileTimeConstant(const_domain) => {
                self.numeric_const(expression, const_domain)
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => self.numeric_conditional(condition, consequent, alternate),
            Expression::IntrinsicBinary { .. } => unsafe {
                let expresssion_type = expression.infer_type();
                let sym = self.get_symbol_for(expression);
                let sort = self.get_sort_for(expresssion_type);
                //todo: use the name to select an appropriate Z3 function
                (
                    expresssion_type.is_floating_point_number(),
                    z3_sys::Z3_mk_const(self.z3_context, sym, sort),
                )
            },
            Expression::InitialParameterValue { path, .. }
            | Expression::UninterpretedCall { path, .. }
            | Expression::UnknownModelField { path, .. }
            | Expression::UnknownTagField { path }
            | Expression::Variable { path, .. } => {
                self.numeric_variable(path, expression.infer_type())
            }
            Expression::IntrinsicBitVectorUnary { .. } => unsafe {
                //todo: use the name to select an appropriate Z3 bitvector function
                let sym = self.get_symbol_for(expression);
                (
                    false,
                    z3_sys::Z3_mk_const(self.z3_context, sym, self.int_sort),
                )
            },
            Expression::IntrinsicFloatingPointUnary { .. } => unsafe {
                //todo: use the name to select an appropriate Z3 floating point function
                let sym = self.get_symbol_for(expression);
                let sort = self.get_sort_for(expression.infer_type());
                (true, z3_sys::Z3_mk_const(self.z3_context, sym, sort))
            },
            Expression::Neg { operand } => self.numeric_neg(operand),
            Expression::Offset { .. } => unsafe {
                use self::ExpressionType::*;
                let expr_type = expression.infer_type();
                let expr_type = match expr_type {
                    Bool | ThinPointer | NonPrimitive => ExpressionType::I128,
                    t => t,
                };
                let is_float = expr_type.is_floating_point_number();
                let sym = self.get_symbol_for(expression);
                let sort = self.get_sort_for(expr_type);
                (is_float, z3_sys::Z3_mk_const(self.z3_context, sym, sort))
            },
            Expression::Reference(path) => self.numeric_reference(path),
            Expression::Shl { left, right } => self.numeric_shl(left, right),
            Expression::Shr { left, right, .. } => self.numeric_shr(left, right),
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => (
                default.expression.infer_type().is_floating_point_number(),
                self.general_switch(discriminator, cases, default, |e| {
                    self.get_as_numeric_z3_ast(e).1
                }),
            ),
            Expression::TaggedExpression { operand, .. } => {
                self.get_as_numeric_z3_ast(&operand.expression)
            }
            Expression::Transmute { operand, .. } => {
                self.get_as_numeric_z3_ast(&operand.expression)
            }
            Expression::Top | Expression::Bottom => unsafe {
                (
                    false,
                    z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.int_sort),
                )
            },
            Expression::WidenedJoin { path, operand } => self.numeric_widen(path, operand),
            _ => unsafe {
                debug!("uninterpreted expression: {:?}", expression);
                let sym = self.get_symbol_for(expression);
                (
                    false,
                    z3_sys::Z3_mk_const(self.z3_context, sym, self.int_sort),
                )
            },
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_binary_var_arg(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        float_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            rm: z3_sys::Z3_ast,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
        int_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            num_args: ::std::os::raw::c_uint,
            args: *const z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> (bool, z3_sys::Z3_ast) {
        let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
        let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        if lf != rf {
            warn!("can't encode {:?} numeric var arg op {:?}", left, right);
            let vt = left.expression.infer_type();
            return (
                vt.is_floating_point_number(),
                self.general_variable(&Path::get_as_path(left.clone()), vt),
            );
        }
        unsafe {
            if lf {
                (
                    true,
                    float_op(self.z3_context, self.nearest_even, left_ast, right_ast),
                )
            } else {
                let tmp = vec![left_ast, right_ast];
                (false, int_op(self.z3_context, 2, tmp.as_ptr()))
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_binary_overflow_vararg(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        result_type: ExpressionType,
        int_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            num_args: ::std::os::raw::c_uint,
            args: *const z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> (bool, z3_sys::Z3_ast) {
        let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
        let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        checked_assume!(!(lf || rf));
        unsafe {
            let tmp = vec![left_ast, right_ast];
            let result = int_op(self.z3_context, 2, tmp.as_ptr());
            let min_ast = self.get_constant_as_ast(&result_type.min_value());
            let min_is_gt = z3_sys::Z3_mk_gt(self.z3_context, min_ast, result);
            let max_ast = self.get_constant_as_ast(&result_type.max_value());
            let max_is_lt = z3_sys::Z3_mk_lt(self.z3_context, max_ast, result);
            let tmp = vec![min_is_gt, max_is_lt];
            let result_overflows = z3_sys::Z3_mk_or(self.z3_context, 2, tmp.as_ptr());
            let left_in_range = self.get_range_check(left_ast, min_ast, max_ast);
            let right_in_range = self.get_range_check(right_ast, min_ast, max_ast);
            let tmp = vec![left_in_range, right_in_range, result_overflows];
            (false, z3_sys::Z3_mk_and(self.z3_context, 3, tmp.as_ptr()))
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_rem(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
    ) -> (bool, z3_sys::Z3_ast) {
        let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
        let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        if lf != rf {
            warn!("can't encode {:?} rem {:?}", left, right);
            let vt = left.expression.infer_type();
            return (
                vt.is_floating_point_number(),
                self.general_variable(&Path::get_as_path(left.clone()), vt),
            );
        }
        unsafe {
            if lf {
                (
                    true,
                    z3_sys::Z3_mk_fpa_rem(self.z3_context, left_ast, right_ast),
                )
            } else {
                let left_type = left.expression.infer_type();
                if left_type.is_unsigned_integer() {
                    (
                        false,
                        z3_sys::Z3_mk_rem(self.z3_context, left_ast, right_ast),
                    )
                } else {
                    (false, {
                        let cond = z3_sys::Z3_mk_lt(self.z3_context, left_ast, self.zero);
                        let rem = z3_sys::Z3_mk_rem(self.z3_context, left_ast, right_ast);
                        let tmp = vec![self.zero, rem];
                        let neg_rem = z3_sys::Z3_mk_sub(self.z3_context, 2, tmp.as_ptr());
                        z3_sys::Z3_mk_ite(self.z3_context, cond, neg_rem, rem)
                    })
                }
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_binary(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        float_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            rm: z3_sys::Z3_ast,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
        int_op: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> (bool, z3_sys::Z3_ast) {
        let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
        let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        if lf != rf {
            warn!("can't encode {:?} numeric op {:?}", left, right);
            let vt = left.expression.infer_type();
            return (
                vt.is_floating_point_number(),
                self.general_variable(&Path::get_as_path(left.clone()), vt),
            );
        }
        unsafe {
            if lf {
                (
                    true,
                    float_op(self.z3_context, self.nearest_even, left_ast, right_ast),
                )
            } else {
                (false, int_op(self.z3_context, left_ast, right_ast))
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_join(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
    ) -> (bool, z3_sys::Z3_ast) {
        unsafe {
            let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
            let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
            if lf != rf {
                warn!("can't encode {:?} join {:?}", left, right);
                let vt = left.expression.infer_type();
                return (
                    vt.is_floating_point_number(),
                    self.general_variable(&Path::get_as_path(left.clone()), vt),
                );
            }
            let sym = self.get_symbol_for(self);
            let condition_ast = z3_sys::Z3_mk_const(self.z3_context, sym, self.bool_sort);
            (
                lf,
                z3_sys::Z3_mk_ite(self.z3_context, condition_ast, left_ast, right_ast),
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_boolean_op(&self, expression: &Expression) -> (bool, z3_sys::Z3_ast) {
        let ast = self.get_as_z3_ast(expression);
        unsafe {
            (
                false,
                z3_sys::Z3_mk_ite(self.z3_context, ast, self.one, self.zero),
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_bitwise_expression(&self, expression: &Expression) -> (bool, z3_sys::Z3_ast) {
        let ast = self.get_as_bv_z3_ast(expression, 128);
        unsafe { (false, z3_sys::Z3_mk_bv2int(self.z3_context, ast, false)) }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_bitwise_not(
        &self,
        operand: &Rc<AbstractValue>,
        result_type: ExpressionType,
    ) -> (bool, z3_sys::Z3_ast) {
        unsafe {
            if result_type.is_signed_integer() {
                let (fp, neg) = self.numeric_neg(operand);
                checked_assume!(!fp); // The Rust type system should prevent this
                let tmp = vec![neg, self.one];
                (false, z3_sys::Z3_mk_sub(self.z3_context, 2, tmp.as_ptr()))
            } else {
                let (fp, ast) = self.get_as_numeric_z3_ast(&operand.expression);
                checked_assume!(!fp); // The Rust type system should prevent this
                let max_ast = self.get_constant_as_ast(&result_type.max_value());
                let tmp = vec![max_ast, ast];
                (false, z3_sys::Z3_mk_sub(self.z3_context, 2, tmp.as_ptr()))
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_cast(
        &self,
        expression: &Expression,
        target_type: ExpressionType,
    ) -> (bool, z3_sys::Z3_ast) {
        unsafe {
            let path_symbol = self.get_symbol_for(expression);
            match target_type {
                ExpressionType::F32 => (
                    true,
                    z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.f32_sort),
                ),
                ExpressionType::F64 => (
                    true,
                    z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.f64_sort),
                ),
                _ => {
                    if target_type.is_integer() || target_type == ExpressionType::Char {
                        let exp_type = expression.infer_type();
                        if exp_type == target_type {
                            self.get_as_numeric_z3_ast(expression)
                        } else if exp_type.is_signed_integer() {
                            // In order to (re-interpret) cast the expr value to unsigned, or
                            // just to safely truncate it, we need to compute the 2's complement.
                            let expr_ast = self.get_as_numeric_z3_ast(expression).1;
                            let modulo_constant = target_type.as_unsigned().modulo_constant();
                            let modulo_ast = if modulo_constant.is_bottom() {
                                let num_str = "340282366920938463463374607431768211456";
                                let c_string = CString::new(num_str).unwrap();
                                z3_sys::Z3_mk_numeral(
                                    self.z3_context,
                                    c_string.into_raw(),
                                    self.int_sort,
                                )
                            } else {
                                self.get_constant_as_ast(&modulo_constant)
                            };
                            let args = vec![expr_ast, modulo_ast];
                            let complement = z3_sys::Z3_mk_add(self.z3_context, 2, args.as_ptr());
                            let is_negative =
                                z3_sys::Z3_mk_lt(self.z3_context, expr_ast, self.zero);
                            let mut unsigned_ast = z3_sys::Z3_mk_ite(
                                self.z3_context,
                                is_negative,
                                complement,
                                expr_ast,
                            );

                            // Truncate the complement by taking its unsigned remainder, if need be
                            if target_type.bit_length() < exp_type.bit_length() {
                                unsigned_ast =
                                    z3_sys::Z3_mk_rem(self.z3_context, unsigned_ast, modulo_ast);
                            }

                            self.transmute_to_signed_if_necessary(
                                target_type,
                                modulo_ast,
                                unsigned_ast,
                            )
                        } else if exp_type.is_unsigned_integer() || exp_type == ExpressionType::Char
                        {
                            let mut unsigned_ast = self.get_as_numeric_z3_ast(expression).1;
                            let modulo_constant = target_type.as_unsigned().modulo_constant();
                            let modulo_ast = if modulo_constant.is_bottom() {
                                let num_str = "340282366920938463463374607431768211456";
                                let c_string = CString::new(num_str).unwrap();
                                z3_sys::Z3_mk_numeral(
                                    self.z3_context,
                                    c_string.into_raw(),
                                    self.int_sort,
                                )
                            } else {
                                self.get_constant_as_ast(&modulo_constant)
                            };

                            // Truncate the expression value if need be
                            if target_type.bit_length() < exp_type.bit_length() {
                                unsigned_ast =
                                    z3_sys::Z3_mk_rem(self.z3_context, unsigned_ast, modulo_ast);
                            }

                            self.transmute_to_signed_if_necessary(
                                target_type,
                                modulo_ast,
                                unsigned_ast,
                            )
                        } else {
                            // Could be a thin pointer or an enum
                            (
                                false,
                                z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.int_sort),
                            )
                        }
                    } else {
                        if target_type != ExpressionType::ThinPointer {
                            // target type is not numeric and not a pointer, but the result of the
                            // cast is expected to be numeric. This probably a mistake.
                            info!(
                                "non numeric cast to {:?} found in numeric context {:?}",
                                target_type, expression
                            );
                        }
                        self.get_as_numeric_z3_ast(expression)
                    }
                }
            }
        }
    }

    fn transmute_to_signed_if_necessary(
        &self,
        target_type: ExpressionType,
        modulo_ast: z3_sys::Z3_ast,
        unsigned_ast: z3_sys::Z3_ast,
    ) -> (bool, z3_sys::Z3_ast) {
        unsafe {
            if target_type.is_signed_integer() {
                // re-interpret the unsigned bits as a signed number by conditionally subtracting
                let max_val_ast = self.get_constant_as_ast(&target_type.max_value());
                let is_positive = z3_sys::Z3_mk_le(self.z3_context, unsigned_ast, max_val_ast);
                let signed_ast =
                    z3_sys::Z3_mk_sub(self.z3_context, 2, vec![unsigned_ast, modulo_ast].as_ptr());
                (
                    false,
                    z3_sys::Z3_mk_ite(self.z3_context, is_positive, unsigned_ast, signed_ast),
                )
            } else {
                // target type is an integer and not signed
                (false, unsigned_ast)
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_const(
        &self,
        expression: &Expression,
        const_domain: &ConstantDomain,
    ) -> (bool, z3_sys::Z3_ast) {
        match const_domain {
            ConstantDomain::Char(..) | ConstantDomain::I128(..) | ConstantDomain::U128(..) => {
                (false, self.get_constant_as_ast(const_domain))
            }
            ConstantDomain::F32(..) | ConstantDomain::F64(..) => {
                (true, self.get_constant_as_ast(const_domain))
            }
            ConstantDomain::False => unsafe {
                (false, z3_sys::Z3_mk_int(self.z3_context, 0, self.int_sort))
            },
            ConstantDomain::True => unsafe {
                (false, z3_sys::Z3_mk_int(self.z3_context, 1, self.int_sort))
            },
            _ => unsafe {
                debug!(
                    "non numeric constant in numeric context: {:?}",
                    const_domain
                );
                let sym = self.get_symbol_for(const_domain);
                (
                    false,
                    z3_sys::Z3_mk_const(self.z3_context, sym, self.int_sort),
                )
            },
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_conditional(
        &self,
        condition: &Rc<AbstractValue>,
        consequent: &Rc<AbstractValue>,
        alternate: &Rc<AbstractValue>,
    ) -> (bool, z3_sys::Z3_ast) {
        let condition_ast = self.get_as_bool_z3_ast(&condition.expression);
        let (cf, consequent_ast) = self.get_as_numeric_z3_ast(&consequent.expression);
        let (af, alternate_ast) = self.get_as_numeric_z3_ast(&alternate.expression);
        checked_assume_eq!(cf, af);
        unsafe {
            (
                cf,
                z3_sys::Z3_mk_ite(
                    self.z3_context,
                    condition_ast,
                    consequent_ast,
                    alternate_ast,
                ),
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_neg(&self, operand: &Rc<AbstractValue>) -> (bool, z3_sys::Z3_ast) {
        let (is_float, operand_ast) = self.get_as_numeric_z3_ast(&operand.expression);
        unsafe {
            if is_float {
                (true, z3_sys::Z3_mk_fpa_neg(self.z3_context, operand_ast))
            } else {
                (
                    false,
                    z3_sys::Z3_mk_unary_minus(self.z3_context, operand_ast),
                )
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_reference(&self, path: &Rc<Path>) -> (bool, z3_sys::Z3_ast) {
        unsafe {
            let path_symbol = self.get_symbol_for(path);
            (
                false,
                z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.int_sort),
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_shl(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
    ) -> (bool, z3_sys::Z3_ast) {
        let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
        let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        checked_assume!(!(lf || rf));
        unsafe {
            let right_power = z3_sys::Z3_mk_power(self.z3_context, self.two, right_ast);
            let tmp = vec![left_ast, right_power];
            (false, z3_sys::Z3_mk_mul(self.z3_context, 2, tmp.as_ptr()))
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_shr(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
    ) -> (bool, z3_sys::Z3_ast) {
        let (lf, left_ast) = self.get_as_numeric_z3_ast(&left.expression);
        let (rf, right_ast) = self.get_as_numeric_z3_ast(&right.expression);
        checked_assume!(!(lf || rf));
        unsafe {
            let right_power = z3_sys::Z3_mk_power(self.z3_context, self.two, right_ast);
            (
                false,
                z3_sys::Z3_mk_div(self.z3_context, left_ast, right_power),
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_variable(
        &self,
        path: &Rc<Path>,
        var_type: ExpressionType,
    ) -> (bool, z3_sys::Z3_ast) {
        use self::ExpressionType::*;
        unsafe {
            let path_symbol = self.get_symbol_for(path);
            let sort = match var_type {
                F32 => self.f32_sort,
                F64 => self.f64_sort,
                _ => self.int_sort,
            };
            let ast = z3_sys::Z3_mk_const(self.z3_context, path_symbol, sort);
            if var_type.is_integer() {
                let min_ast = self.get_constant_as_ast(&var_type.min_value());
                let max_ast = self.get_constant_as_ast(&var_type.max_value());
                let range_check = self.get_range_check(ast, min_ast, max_ast);

                // Side-effecting the solver smells bad, but it hard to come up with an expression
                // of type var_type that only take values that satisfies the range constraint.
                // Since this is kind of a lazy variable declaration, it is probably OK.

                // It turns out that if there were previous calls to the smt solver that produced strings
                // this call will crash
                z3_sys::Z3_solver_assert(self.z3_context, self.z3_solver, range_check);
            }
            (var_type.is_floating_point_number(), ast)
        }
    }

    #[logfn_inputs(TRACE)]
    fn numeric_widen(
        &self,
        path: &Rc<Path>,
        operand: &Rc<AbstractValue>,
    ) -> (bool, z3_sys::Z3_ast) {
        use self::ExpressionType::*;
        let expr_type = match operand.expression.infer_type() {
            Bool | ThinPointer | NonPrimitive | Unit => ExpressionType::I128,
            val => val,
        };
        let is_float = expr_type.is_floating_point_number();
        let ast = self.get_ast_for_widened(path, operand, expr_type);
        (is_float, ast)
    }

    #[logfn_inputs(TRACE)]
    fn get_as_bool_z3_ast(&self, expression: &Expression) -> z3_sys::Z3_ast {
        match expression {
            Expression::BitAnd { .. } | Expression::BitOr { .. } | Expression::BitXor { .. } => {
                //todo: get operands as booleans and treat these operands as logical
                let bv = self.get_as_bv_z3_ast(expression, 128);
                unsafe {
                    let i = z3_sys::Z3_mk_bv2int(self.z3_context, bv, false);
                    let f = z3_sys::Z3_mk_eq(self.z3_context, i, self.zero);
                    z3_sys::Z3_mk_not(self.z3_context, f)
                }
            }
            Expression::CompileTimeConstant(const_domain) => match const_domain {
                ConstantDomain::False => unsafe { z3_sys::Z3_mk_false(self.z3_context) },
                ConstantDomain::True => unsafe { z3_sys::Z3_mk_true(self.z3_context) },
                ConstantDomain::U128(val) => unsafe {
                    if *val == 0 {
                        z3_sys::Z3_mk_false(self.z3_context)
                    } else {
                        z3_sys::Z3_mk_true(self.z3_context)
                    }
                },
                _ => self.get_as_z3_ast(expression),
            },
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let condition_ast = self.get_as_bool_z3_ast(&condition.expression);
                let consequent_ast = self.get_as_bool_z3_ast(&consequent.expression);
                let alternate_ast = self.get_as_bool_z3_ast(&alternate.expression);
                unsafe {
                    z3_sys::Z3_mk_ite(
                        self.z3_context,
                        condition_ast,
                        consequent_ast,
                        alternate_ast,
                    )
                }
            }
            Expression::Join { left, right } => self.boolean_join(left, right),
            Expression::Reference(path) => unsafe {
                let path_symbol = self.get_symbol_for(path);
                z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.bool_sort)
            },
            Expression::Switch {
                discriminator,
                cases,
                default,
            } => self.general_switch(discriminator, cases, default, |e| {
                self.get_as_bool_z3_ast(e)
            }),
            Expression::Top | Expression::Bottom => unsafe {
                z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.bool_sort)
            },
            Expression::UninterpretedCall {
                result_type: var_type,
                path,
                ..
            }
            | Expression::InitialParameterValue { path, var_type }
            | Expression::Variable { path, var_type } => {
                if *var_type != ExpressionType::Bool {
                    debug!("path {:?}, type {:?}", path, var_type);
                }
                unsafe {
                    let path_symbol = self.get_symbol_for(path);
                    z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.bool_sort)
                }
            }
            Expression::WidenedJoin { path, operand } => {
                self.get_ast_for_widened(path, operand, ExpressionType::Bool)
            }
            _ => {
                let expression_type = expression.infer_type();
                if expression_type.is_integer() {
                    let (_, ast) = self.get_as_numeric_z3_ast(expression);
                    unsafe {
                        z3_sys::Z3_mk_not(
                            self.z3_context,
                            z3_sys::Z3_mk_eq(self.z3_context, ast, self.zero),
                        )
                    }
                } else {
                    self.get_as_z3_ast(expression)
                }
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn get_as_bv_z3_ast(&self, expression: &Expression, num_bits: u32) -> z3_sys::Z3_ast {
        match expression {
            Expression::Add { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvadd)
            }
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => self.bv_overflows(
                left,
                right,
                *result_type,
                z3_sys::Z3_mk_bvadd_no_overflow,
                z3_sys::Z3_mk_bvadd_no_underflow,
            ),
            Expression::Div { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvsdiv)
            }
            Expression::Mul { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvmul)
            }
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => self.bv_overflows(
                left,
                right,
                *result_type,
                z3_sys::Z3_mk_bvmul_no_overflow,
                z3_sys::Z3_mk_bvmul_no_underflow,
            ),
            Expression::Rem { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvsrem)
            }
            Expression::Sub { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvsub)
            }
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => self.bv_overflows(
                left,
                right,
                *result_type,
                z3_sys::Z3_mk_bvsub_no_underflow,
                z3_sys::Z3_mk_bvsub_no_overflow,
            ),
            Expression::And { .. }
            | Expression::Equals { .. }
            | Expression::GreaterOrEqual { .. }
            | Expression::GreaterThan { .. }
            | Expression::LessOrEqual { .. }
            | Expression::LessThan { .. }
            | Expression::LogicalNot { .. }
            | Expression::Ne { .. }
            | Expression::Or { .. } => self.bv_boolean_op(expression, num_bits),
            Expression::BitAnd { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvand)
            }
            Expression::BitNot {
                operand,
                result_type,
            } => self.bv_not(num_bits, operand, *result_type),
            Expression::BitOr { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvor)
            }
            Expression::BitXor { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvxor)
            }
            Expression::Cast {
                target_type,
                operand,
            } => self.bv_cast(&operand.expression, *target_type, num_bits),
            Expression::CompileTimeConstant(const_domain) => {
                self.bv_constant(num_bits, const_domain)
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => self.bv_conditional(num_bits, condition, consequent, alternate),
            Expression::IntrinsicBitVectorUnary { .. } => unsafe {
                //todo: use the name to select an appropriate Z3 bitvector function
                let sym = self.get_symbol_for(expression);
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                z3_sys::Z3_mk_const(self.z3_context, sym, sort)
            },
            Expression::Join { left, right, .. } => self.bv_join(left, right, num_bits),
            Expression::Neg { operand } => self.bv_neg(num_bits, operand),
            Expression::Offset { .. } => unsafe {
                let sym = self.get_symbol_for(expression);
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                z3_sys::Z3_mk_const(self.z3_context, sym, sort)
            },
            Expression::Reference(path) => self.bv_reference(num_bits, path),
            Expression::Shl { left, right } => {
                self.bv_binary(num_bits, left, right, z3_sys::Z3_mk_bvshl)
            }
            Expression::Shr { left, right } => self.bv_shr_by(num_bits, left, right),
            Expression::Top | Expression::Bottom => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, sort)
            },
            Expression::Transmute { .. } => unsafe {
                let sym = self.get_symbol_for(expression);
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                z3_sys::Z3_mk_const(self.z3_context, sym, sort)
            },
            Expression::UninterpretedCall { path, .. }
            | Expression::InitialParameterValue { path, .. }
            | Expression::Variable { path, .. } => self.bv_variable(path, num_bits),
            Expression::WidenedJoin { path, .. } => self.bv_widen(path, num_bits),
            _ => {
                let path = Path::get_as_path(AbstractValue::make_from(expression.clone(), 1));
                self.bv_variable(&path, num_bits)
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_binary(
        &self,
        num_bits: u32,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        operation: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> z3_sys::Z3_ast {
        let left_ast = self.get_as_bv_z3_ast(&left.expression, num_bits);
        let right_ast = self.get_as_bv_z3_ast(&right.expression, num_bits);
        unsafe { operation(self.z3_context, left_ast, right_ast) }
    }

    #[logfn_inputs(TRACE)]
    fn bv_neg(&self, num_bits: u32, operand: &Rc<AbstractValue>) -> z3_sys::Z3_ast {
        let ast = self.get_as_bv_z3_ast(&operand.expression, num_bits);
        unsafe { z3_sys::Z3_mk_bvneg(self.z3_context, ast) }
    }

    #[logfn_inputs(TRACE)]
    fn bv_not(
        &self,
        num_bits: u32,
        operand: &Rc<AbstractValue>,
        result_type: ExpressionType,
    ) -> z3_sys::Z3_ast {
        let ast = self.get_as_bv_z3_ast(&operand.expression, num_bits);
        unsafe { z3_sys::Z3_mk_bvnot(self.z3_context, ast) }
    }

    #[logfn_inputs(TRACE)]
    fn bv_overflows(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        result_type: ExpressionType,
        no_overflow: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
            signed: bool,
        ) -> z3_sys::Z3_ast,
        no_underflow: unsafe extern "C" fn(
            c: z3_sys::Z3_context,
            t1: z3_sys::Z3_ast,
            t2: z3_sys::Z3_ast,
        ) -> z3_sys::Z3_ast,
    ) -> z3_sys::Z3_ast {
        let num_bits = u32::from(result_type.bit_length());
        let is_signed = result_type.is_signed_integer();
        let left_bv = self.get_as_bv_z3_ast(&left.expression, num_bits);
        let right_bv = self.get_as_bv_z3_ast(&right.expression, num_bits);
        unsafe {
            let does_not_overflow = no_overflow(self.z3_context, left_bv, right_bv, is_signed);
            if is_signed {
                let does_not_underflow = no_underflow(self.z3_context, left_bv, right_bv);
                let tmp = vec![does_not_overflow, does_not_underflow];
                let stays_in_range = z3_sys::Z3_mk_and(self.z3_context, 2, tmp.as_ptr());
                z3_sys::Z3_mk_not(self.z3_context, stays_in_range)
            } else {
                z3_sys::Z3_mk_not(self.z3_context, does_not_overflow)
            }
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_boolean_op(&self, expression: &Expression, num_bits: u32) -> z3_sys::Z3_ast {
        let ast = self.get_as_z3_ast(expression);
        // ast results in a boolean, but we want a bit vector.
        unsafe {
            let bv_true = self.bv_constant(num_bits, &ConstantDomain::True);
            let bv_false = self.bv_constant(num_bits, &ConstantDomain::False);
            z3_sys::Z3_mk_ite(self.z3_context, ast, bv_true, bv_false)
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_cast(
        &self,
        expression: &Expression,
        target_type: ExpressionType,
        num_bits: u32,
    ) -> z3_sys::Z3_ast {
        let ast = self.get_as_bv_z3_ast(expression, num_bits);
        let mask = self.bv_constant(num_bits, &target_type.max_value());
        unsafe { z3_sys::Z3_mk_bvand(self.z3_context, ast, mask) }
    }

    #[logfn_inputs(TRACE)]
    fn bv_constant(&self, num_bits: u32, const_domain: &ConstantDomain) -> z3_sys::Z3_ast {
        match const_domain {
            ConstantDomain::Char(v) => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let num_str = format!("{}", (*v as u128));
                let c_string = CString::new(num_str).unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            ConstantDomain::False => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let c_string = CString::new("0").unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            ConstantDomain::F32(v) => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let num_str = format!("{}", *v);
                let c_string = CString::new(num_str).unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            ConstantDomain::F64(v) => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let num_str = format!("{}", *v);
                let c_string = CString::new(num_str).unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            ConstantDomain::I128(v) => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let num_str = format!("{}", (*v as u128));
                let c_string = CString::new(num_str).unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            ConstantDomain::U128(v) => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let num_str = format!("{}", *v);
                let c_string = CString::new(num_str).unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            ConstantDomain::True => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                let c_string = CString::new("1").unwrap();
                z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), sort)
            },
            _ => unsafe {
                let sym = self.get_symbol_for(const_domain);
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                z3_sys::Z3_mk_const(self.z3_context, sym, sort)
            },
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_conditional(
        &self,
        num_bits: u32,
        condition: &Rc<AbstractValue>,
        consequent: &Rc<AbstractValue>,
        alternate: &Rc<AbstractValue>,
    ) -> z3_sys::Z3_ast {
        let condition_ast = self.get_as_bool_z3_ast(&condition.expression);
        let consequent_ast = self.get_as_bv_z3_ast(&consequent.expression, num_bits);
        let alternate_ast = self.get_as_bv_z3_ast(&alternate.expression, num_bits);
        unsafe {
            z3_sys::Z3_mk_ite(
                self.z3_context,
                condition_ast,
                consequent_ast,
                alternate_ast,
            )
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_join(
        &self,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
        num_bits: u32,
    ) -> z3_sys::Z3_ast {
        let left_ast = self.get_as_bv_z3_ast(&left.expression, num_bits);
        let right_ast = self.get_as_bv_z3_ast(&right.expression, num_bits);
        unsafe {
            let sym = self.get_symbol_for(self);
            let condition_ast = z3_sys::Z3_mk_const(self.z3_context, sym, self.bool_sort);
            z3_sys::Z3_mk_ite(self.z3_context, condition_ast, left_ast, right_ast)
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_reference(&self, num_bits: u32, path: &Rc<Path>) -> z3_sys::Z3_ast {
        unsafe {
            let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
            let path_symbol = self.get_symbol_for(path);
            z3_sys::Z3_mk_const(self.z3_context, path_symbol, sort)
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_shr_by(
        &self,
        num_bits: u32,
        left: &Rc<AbstractValue>,
        right: &Rc<AbstractValue>,
    ) -> z3_sys::Z3_ast {
        let left_type = left.expression.infer_type();
        let left_ast = self.get_as_bv_z3_ast(&left.expression, num_bits);
        let right_ast = self.get_as_bv_z3_ast(&right.expression, num_bits);
        unsafe {
            if left_type.is_signed_integer() {
                z3_sys::Z3_mk_bvashr(self.z3_context, left_ast, right_ast)
            } else {
                z3_sys::Z3_mk_bvlshr(self.z3_context, left_ast, right_ast)
            }
        }
    }

    fn switch_with_bv_discriminator<F>(
        &self,
        discriminator: &Rc<AbstractValue>,
        cases: &[(Rc<AbstractValue>, Rc<AbstractValue>)],
        default: &Rc<AbstractValue>,
        get_result_ast: F,
    ) -> z3_sys::Z3_ast
    where
        F: FnOnce(&Expression) -> z3_sys::Z3_ast + Copy,
    {
        trace!(
            "switch_with_bv_discriminator(discriminator {:?}, cases: {:?}, default {:?})",
            discriminator,
            cases,
            default
        );
        let ty = discriminator.expression.infer_type();
        let num_bits = u32::from(ty.bit_length());
        let discriminator_ast = self.get_as_bv_z3_ast(&discriminator.expression, num_bits);
        let default_ast = get_result_ast(&default.expression);
        cases
            .iter()
            .fold(default_ast, |acc_ast, (case_val, case_result)| unsafe {
                let case_val_ast = self.get_as_bv_z3_ast(&case_val.expression, num_bits);
                let cond_ast = z3_sys::Z3_mk_eq(self.z3_context, discriminator_ast, case_val_ast);
                let case_result_ast = get_result_ast(&case_result.expression);
                z3_sys::Z3_mk_ite(self.z3_context, cond_ast, case_result_ast, acc_ast)
            })
    }

    #[logfn_inputs(TRACE)]
    fn bv_variable(&self, path: &Rc<Path>, num_bits: u32) -> z3_sys::Z3_ast {
        unsafe {
            let path_symbol = self.get_symbol_for(path);
            let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
            z3_sys::Z3_mk_const(self.z3_context, path_symbol, sort)
        }
    }

    #[logfn_inputs(TRACE)]
    fn bv_widen(&self, path: &Rc<Path>, num_bits: u32) -> z3_sys::Z3_ast {
        self.bv_variable(path, num_bits)
    }
}
