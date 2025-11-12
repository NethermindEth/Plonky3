use p3_baby_bear::BabyBear;
use p3_field::*;
use p3_matrix::Matrix;

use crate::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, air, symbolic_builder::SymbolicAirBuilder,
};

pub struct IsZeroAir {}

// x, y, z
const NUM_ADD_COLS: usize = 3;

impl<F> BaseAir<F> for IsZeroAir {
    fn width(&self) -> usize {
        NUM_ADD_COLS
    }
}

impl<AB: AirBuilder> Air<AB> for IsZeroAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0).expect("Matrix is empty?");
        
        // z * x = 0
        builder.assert_eq(local[2] * local[0], AB::F::ZERO);

        // (z - 1) * (x * y - 1) = 0
        builder.assert_eq((local[2] - AB::F::ONE) * (local[0] * local[1] - AB::F::ONE), AB::F::ZERO);

        // z^2 - z = 0
        builder.assert_eq(local[2] * local[2] - local[2], AB::F::ZERO);
    }
}

#[test]
fn extract_is_zero() {
    let air = IsZeroAir {};
    let mut sbuilder = SymbolicAirBuilder::<BabyBear, BabyBear, ()>::new(0, NUM_ADD_COLS, 0, 0);
    air.eval(&mut sbuilder);
    sbuilder.print_lean_constraints();
}
