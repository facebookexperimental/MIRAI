// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc::hir::{self, itemlikevisit, ImplItemKind, ItemKind, TraitItemKind, TraitMethod};
use rustc::ty::TyCtxt;
use rustc_driver::driver;

/// Holds the state for the crate visitor.
pub struct CrateVisitor<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub state: &'a driver::CompileState<'a, 'tcx>,
}

/// Provides methods that are called by Crate.visit_all_item_likes whenever it traverses
/// to an item like node. We use this to identify functions and methods that might have
/// code to analyze.
impl<'a, 'tcx: 'a, 'hir> itemlikevisit::ItemLikeVisitor<'hir> for CrateVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &'hir hir::Item) {
        if let ItemKind::Fn(.., body_id) = item.node {
            let did = self.tcx.hir.body_owner_def_id(body_id);
            info!("analyzing {}", self.tcx.def_path_debug_str(did));
        }
    }
    fn visit_trait_item(&mut self, trait_item: &'hir hir::TraitItem) {
        if let TraitItemKind::Method(.., TraitMethod::Provided(body_id)) = trait_item.node {
            let did = self.tcx.hir.body_owner_def_id(body_id);
            info!("analyzing {}", self.tcx.def_path_debug_str(did));
        }
    }
    fn visit_impl_item(&mut self, impl_item: &'hir hir::ImplItem) {
        if let ImplItemKind::Method(.., body_id) = impl_item.node {
            let did = self.tcx.hir.body_owner_def_id(body_id);
            info!("analyzing {}", self.tcx.def_path_debug_str(did));
        }
    }
}

// todo: remove this once issue #10 is resolved.
trait TestTrait {
    #[cfg_attr(tarpaulin, skip)]
    fn test_method() {}
}
