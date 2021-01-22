macro_rules! add_with_overflow {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> ($tt, bool) {
            let result = (x as $tt) + (y as $tt);
            (result % (($m as $tt) + 1), result > ($m as $tt))
        }
    };
}

macro_rules! atomic_int {
    ($n:ident, $t:ty, $op:tt) => {
        pub unsafe fn $n(dst: *mut $t, src: $t) -> $t {
            let result = *dst;
            *dst $op src;
            result
        }
    };
}

// No preconditions needed and no post conditions provided.
// No side-effects and can be safely used as an uninterpreted function.
macro_rules! default_contract {
    ($n:ident) => {
        pub fn $n<T>() -> T {
            result!()
        }
    };
}

macro_rules! exact_div {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            precondition!(x % y == 0);
            x / y
        }
    };
}

macro_rules! exact_signed_div {
    ($t:ty, $n:ident, $m:expr) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            precondition!(x != $m || y != -1);
            precondition!(x % y == 0);
            x / y
        }
    };
}

macro_rules! rotate_left {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            let bw = std::intrinsics::size_of::<$t>() as $t;
            (x << (y % bw)) | (x >> ((bw - y) % bw))
        }
    };
}

macro_rules! rotate_right {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            let bw = std::intrinsics::size_of::<$t>() as $t;
            (x << ((bw - y) % bw)) | (x >> (y % bw))
        }
    };
}

macro_rules! saturating_add {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $t {
            let result = (a as $tt) + (b as $tt);
            if result > ($m as $tt) {
                $m
            } else {
                result as $t
            }
        }
    };
}

macro_rules! saturating_sub {
    ($t:ty, $n:ident) => {
        pub fn $n(a: $t, b: $t) -> $t {
            if a < b {
                0
            } else {
                a - b
            }
        }
    };
}

macro_rules! sub_with_overflow {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> ($t, bool) {
            let result = (x as $tt) + (-(y as $tt));
            (
                (result % (($m as $tt) + 1)) as $t,
                result < 0 || result > ($m as $tt),
            )
        }
    };
}

macro_rules! unchecked_add {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!((x as $tt) + (y as $tt) <= ($m as $tt));
            x + y
        }
    };
}

macro_rules! unchecked_div {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            x / y
        }
    };
}

macro_rules! unchecked_signed_div {
    ($t:ty, $n:ident, $m:expr) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            precondition!(x != $m || y != -1);
            x / y
        }
    };
}

macro_rules! unchecked_mul {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!((x as $tt) * (y as $tt) <= ($m as $tt));
            x * y
        }
    };
}

macro_rules! unchecked_rem {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            x % y
        }
    };
}

macro_rules! unchecked_shl {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y <= (std::intrinsics::size_of::<$t>() as $t));
            x << y
        }
    };
}

macro_rules! unchecked_shr {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y <= (std::intrinsics::size_of::<$t>() as $t));
            x >> y
        }
    };
}

macro_rules! unchecked_signed_rem {
    ($t:ty, $n:ident, $m:expr) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            precondition!(x != $m || y != -1);
            x % y
        }
    };
}

macro_rules! unchecked_sub {
    ($t:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!((x as i128) - (y as i128) >= 0);
            precondition!((x as i128) - (y as i128) <= ($m as i128));
            x - y
        }
    };
}

macro_rules! wrapping_add {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $tt {
            ((a as $tt) + (b as $tt)) % (($m as $tt) + 1)
        }
    };
}

macro_rules! wrapping_mul {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $tt {
            ((a as $tt) * (b as $tt)) % (($m as $tt) + 1)
        }
    };
}

macro_rules! wrapping_sub {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $t {
            (((a as $tt) + (-(b as $tt))) % (($m as $tt) + 1)) as $t
        }
    };
}
