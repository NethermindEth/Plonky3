use p3_baby_bear::BabyBear;
use p3_field::*;
use p3_matrix::Matrix;

use crate::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, air, symbolic_builder::SymbolicAirBuilder,
};

pub struct FibonacciAir {}

const NUM_ADD_COLS: usize = 12;

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize {
        NUM_ADD_COLS
    }
}

impl<AB: AirBuilder> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let (local) = (main.row_slice(0).expect("Matrix is empty?"));

        let x = <AB as air::AirBuilder>::Expr::from(local[2]);
        // a + b = c + 2^8 * r
        let y = local[2];
        builder.assert_eq::<<AB as air::AirBuilder>::Expr, <AB as air::AirBuilder>::Expr>(
            local[0] + local[1],
            (<AB as air::AirBuilder>::Expr::from(local[3]) * AB::F::from_u32(256)) + y,
        );
    }
}

#[test]
fn extract_fib() {
    let air = FibonacciAir {};
    let mut sbuilder = SymbolicAirBuilder::<BabyBear, BabyBear, ()>::new(0, 2, 0, 0);
    air.eval(&mut sbuilder);
    sbuilder.print_lean_constraints();
}

