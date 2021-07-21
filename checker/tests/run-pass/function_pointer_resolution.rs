// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that function pointers get resolved

// MIRAI_FLAGS --single_func=function_pointer_resolution.bench.run

pub mod traits {
    pub mod lib {
        pub trait FooTrait {
            fn method(&self) -> u32;
        }

        pub trait BarTrait {
            fn method(&self) -> u32;
            fn another_method(&self) -> u32;
            fn yet_another_method(&self) -> u32;
        }

        pub trait BazTrait {
            fn another_method(&self) -> u32;
        }

        pub trait GenericFooTrait<T> {
            fn method(&self) -> T;
        }

        pub mod bounds {
            pub trait BoundTrait {
                fn method(&self) -> i32;
            }
        }

        pub trait MacroTrait {
            fn method(&self) -> u32;
            fn another_method(&self) -> u32;
        }

        pub trait DefaultTrait {
            fn default_method(&self) -> u32 {
                0
            }

            // In order to be able to do dynamic dispatch on DefaultTrait it has to be a Sized type.
            // By default traits are Unsized types.
            fn default_method_no_self() -> u32
            where
                Self: Sized,
            {
                0
            }
        }
    }
}

pub mod structs {
    pub mod lib {
        pub mod fat {
            use crate::traits::lib::BarTrait;
            use crate::traits::lib::BazTrait;
            use crate::traits::lib::DefaultTrait;
            use crate::traits::lib::FooTrait;

            pub struct Fat(pub u32);

            impl Fat {
                pub fn method(&self) -> u32 {
                    self.0
                }

                // Note the mut modifier on self. Method lookup is done for each type in order as described in
                // https://doc.rust-lang.org/reference/expressions/method-call-expr.html. &self and &mut self
                // are different types and &self methods are looked up first including the type's inherent
                // methods and any methods provided by a visible trait implemented by the type.
                pub fn another_method(&mut self) -> u32 {
                    self.0 + 1
                }

                // Note the pub modifier missing from the method signature, rendering it invisible to the
                // outside world.
                #[allow(dead_code)]
                fn yet_another_method(&self) -> u32 {
                    self.0 + 2
                }

                pub fn default_method_no_self() -> u32 {
                    1
                }
            }

            impl FooTrait for Fat {
                fn method(&self) -> u32 {
                    self.0 + 10
                }
            }

            impl BarTrait for Fat {
                fn method(&self) -> u32 {
                    self.0 + 100
                }

                fn another_method(&self) -> u32 {
                    self.0 + 101
                }

                fn yet_another_method(&self) -> u32 {
                    self.0 + 102
                }
            }

            impl BazTrait for Fat {
                fn another_method(&self) -> u32 {
                    self.0 + 1001
                }
            }

            impl DefaultTrait for Fat {
                fn default_method(&self) -> u32 {
                    1
                }

                fn default_method_no_self() -> u32 {
                    2
                }
            }
        }
        pub mod thin {
            use crate::traits::lib::DefaultTrait;
            use crate::traits::lib::FooTrait;
            use crate::traits::lib::GenericFooTrait;

            pub struct Thin;

            impl FooTrait for Thin {
                fn method(&self) -> u32 {
                    0
                }
            }

            impl GenericFooTrait<i32> for Thin {
                fn method(&self) -> i32 {
                    42
                }
            }

            impl GenericFooTrait<u32> for Thin {
                fn method(&self) -> u32 {
                    42
                }
            }

            impl DefaultTrait for Thin {}
        }

        pub struct One;

        impl One {
            pub fn method_1() -> i32 {
                1
            }

            pub fn method_2(&mut self) -> i32 {
                2
            }
        }

        pub struct Two(i32);

        impl Two {
            pub fn new(num: i32) -> Self {
                Two(num)
            }

            pub fn method_1(&self) -> i32 {
                self.0 + 1
            }

            pub fn method_2(&mut self) -> i32 {
                // instance method call (inherent)
                // structs::lib::Two::add_one
                // Call to inherent private method inside another method.
                self.add_one();

                // instance method call (inherent)
                // structs::lib::Two::method_1
                // Call to inherent public method inside another method.
                self.method_1()
            }

            pub fn add_one(&mut self) {
                self.0 = self.0 + 1;
            }
        }
    }
}

pub mod lib {
    use crate::structs::lib::fat::Fat;
    use crate::traits::lib::FooTrait;

    pub type FatMethod = fn(&Fat) -> u32;
    pub type FooMethod = fn(&dyn FooTrait) -> u32;
    pub type GenMethod<T> = fn(&T) -> u32;

    pub fn indirection(foo: &Fat, fun: FatMethod) -> u32 {
        // function pointer call
        // for<'r> fn(&'r structs::lib::fat::Fat) -> u32
        // Call via function pointer 'fun'.
        fun(foo)
    }

    pub fn indirection_generic<T: FooTrait>(foo: &T, fun: GenMethod<T>) -> u32 {
        // function pointer call
        // for<'r> fn(&'r T) -> u32
        // Call via generic function pointer 'fun'.
        fun(foo)
    }

    // Equivalent to indirection(foo: &Fat, fun: FatMethod) -> u32
    // fn indirection_concretized_generic(foo: &Fat, fun: GenMethod<Fat>) -> u32 {
    //     fun(foo)
    // }

    pub fn indirection_trait_object(foo: &dyn FooTrait, fun: FooMethod) -> u32 {
        // function pointer call
        // for<'r> fn(&'r (dyn traits::lib::FooTrait + 'r)) -> u32
        // Call via function pointer 'fun', which accepts a trait object as argument.
        fun(foo)
    }

    // Equivalent to indirection_trait_object(foo: &dyn FooTrait, fun: FooMethod) -> u32
    // fn indirection_sixth(foo: impl FooTrait + 'static, fun: GenMethod<dyn FooTrait>) -> u32 {
    //     fun(&foo)
    // }

    pub fn indirection_fn_trait(foo: &Fat, fun: &dyn Fn(&Fat) -> u32) -> u32 {
        // instance method call (trait - std::ops::Fn::call)
        // &dyn for<'r> std::ops::Fn(&'r structs::lib::fat::Fat) -> u32
        // Call of Fn trait instance 'fun'.
        fun(foo)
    }
}

pub mod bench {
    use crate::lib::indirection;
    use crate::lib::indirection_fn_trait;
    use crate::lib::indirection_generic;
    use crate::lib::indirection_trait_object;
    use crate::structs::lib::fat::Fat;
    use crate::traits::lib::BarTrait;
    use crate::traits::lib::FooTrait;

    mod helpers {
        use super::FooTrait;

        // 'm1' and 'm2' share the same function signature if we ignore the function name. However,
        // 'm1' is not called directly or indirectly (through a function pointer) in comparison to
        // 'm2'. Nevertheless, an imprecise analysis might include both as possible targets of a
        // function pointer call where actually 'm2' is the only pointed function. Such an analysis
        // is sound as the function signatures match, meaning that a variable that points to 'm2'
        // could also point to 'm1'.
        #[allow(dead_code)]
        pub fn m1(obj: &dyn FooTrait) -> u32 {
            obj.method()
        }

        pub fn m2(obj: &dyn FooTrait) -> u32 {
            obj.method()
        }
    }

    pub fn run() {
        let f = Fat(10);

        // static function call
        // function_pointers::lib::indirection
        // Pointed function is part of Fat's implementation (struct impl).
        indirection(&f, Fat::method);

        // static function call
        // function_pointers::lib::indirection
        // Pointed function is part of FooTrait's implementation by Fat (trait impl).
        indirection(&f, FooTrait::method);

        // static function call
        // function_pointers::lib::indirection
        // Pointed function is part of BarTrait's implementation by Fat (trait impl). The syntax
        // used to specify the method is slightly different than in the last testcase but normally
        // there should not be any significant difference. We include this case for completeness.
        indirection(&f, <Fat as BarTrait>::method);

        // static function call
        // function_pointers::lib::indirection_generic
        // Pointed function is generic.
        indirection_generic(&f, Fat::method);
        // The following two calls should be covered by the 'indirection' testcases.
        // indirection_generic(&f, FooTrait::method);
        // indirection_generic(&f, <Fat as BarTrait>::method);

        // static function call
        // function_pointers::lib::indirection_generic
        // Pointed function accepts a trait object as an argument.
        indirection_trait_object(&f, helpers::m2);

        // static function call
        // function_pointers::lib::indirection_fn_trait
        indirection_fn_trait(&f, &Fat::method);
        // The following two calls should be covered by the 'indirection' testcases.
        // indirection_fn_trait(&f, &BarTrait::method);
        // indirection_fn_trait(&f, &<Fat as FooTrait>::method);
    }
}

pub fn main() {}
