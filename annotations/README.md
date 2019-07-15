# MIRAI Annotations

This crate provides a set of macros that can be used in the place of the standard RUST assert and debug_assert macros.
They add value by allowing [MIRAI](https://github.com/facebookexperimental/MIRAI) to:
* distinguish between path conditions and verification conditions
* distinguish between conditions that it should assume as true and conditions that it should verify
* check conditions at compile time that should not be checked at runtime because they are too expensive

From this it follows that we have three families of macros:
* assume macros
* postcondition macros (like verify wehre defined and like assume for callers)
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

Additionally there is also assumed_postcondition! which is an assume at the definition site, rather than a verify.

This crate also provides macros for describing and constraining abstract state that only has meaning to MIRAI. These are:
* get_model_field!
* result!
* set_model_field!

See the documentation for details on how to use these.