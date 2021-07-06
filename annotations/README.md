# MIRAI Annotations

This crate provides a set of macros that can be used in the place of the standard RUST assert and debug_assert macros.
They add value by allowing [MIRAI](https://github.com/facebookexperimental/MIRAI) to:
* distinguish between path conditions and verification conditions
* distinguish between conditions that it should assume as true and conditions that it should verify
* check conditions at compile time that should not be checked at runtime because they are too expensive

From these considerations we get these families of macros:
* assume macros
* postcondition macros (like verify where defined and like assume for callers)
* precondition macros (like assume where defined and like verify for callers)
* verify macros

Each of these has three kinds
* only checked at compile time ('macro' with macro among {assume, precondition, verify})
* always checked at runtime ('checked_macro')
* checked at runtime only for debug builds ('debug_checked_macro')

Additionally, the runtime checked kinds provides eq and ne varieties, leaving us (for assume) with:
* assume!
* checked_assume!
* checked_assume_eq!
* checked_assume_ne!
* debug_checked_assume!
* debug_checked_assume_eq!
* debug_checked_assume_ne!

Likewise for postcondition! precondition! and verify!

Additionally we also have:
* assumed_postcondition! which is an assume at the definition site, rather than a verify.
* assume_preconditions! which assumes that the caller has satisfied all (inferred) preconditions of the next call.
* assume_unreachable! which assumes that it is unreachable for reasons beyond what MIRAI can reason about.
* unrecoverable! which is the same as panic! but explicitly indicates that this is not a programming mistake to reach this.
* verify_unreachable! which requires MIRAI to verify that it is not reachable.

This crate also provides macros for describing and constraining abstract state that only has meaning to MIRAI. These are:
* abstract_value!
* add_tag!
* does_not_have_tag!  
* get_model_field!
* has_tag!  
* result!
* set_model_field!

See the documentation for details on how to use these.