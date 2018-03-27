/// Overflowing math operations.
pub trait Overflowing: Sized {
    fn overflowing_add(self, rhs: Self) -> (Self, bool);
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);

    fn overflowing_div(self, rhs: Self) -> (Self, bool);
    fn overflowing_rem(self, rhs: Self) -> (Self, bool);
    fn overflowing_neg(self) -> (Self, bool);

    fn overflowing_shl(self, rhs: u32) -> (Self, bool);
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
}

macro_rules! overflowing_impl {
    ($trait_name : ident for $($t : ty)*) => {$(
        impl $trait_name for $t {
            #[inline]
            fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                Self::overflowing_add(self, rhs)
            }

            #[inline]
            fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                Self::overflowing_sub(self, rhs)
            }

            #[inline]
            fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                Self::overflowing_mul(self, rhs)
            }

            #[inline]
            fn overflowing_div(self, rhs: Self) -> (Self, bool) {
                Self::overflowing_div(self, rhs)
            }

            #[inline]
            fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
                Self::overflowing_rem(self, rhs)
            }

            #[inline]
            fn overflowing_neg(self) -> (Self, bool) {
                Self::overflowing_neg(self)
            }

            #[inline]
            fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
                Self::overflowing_shl(self, rhs)
            }

            #[inline]
            fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
                Self::overflowing_shr(self, rhs)
            }
        }
    )*}
}

overflowing_impl!(Overflowing for isize usize i8 u8 i16 u16 i32 u32 i64 u64);
