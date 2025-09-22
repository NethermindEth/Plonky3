use p3_baby_bear::BabyBear;
use p3_matrix::Matrix;

use crate::{symbolic_builder::SymbolicAirBuilder, Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};

pub struct FibonacciAir {}

const NUM_FIBONACCI_COLS: usize = 2;

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize {
        NUM_FIBONACCI_COLS
    }
}



impl<AB: AirBuilder> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let (local, _) = (
            main.row_slice(0).expect("Matrix is empty?"),
            main.row_slice(1).expect("Matrix only has 1 row?"),
        );

        builder.assert_eq(local[0], local[1]);

    }
}

#[test]
fn extract_fib() {
    let air = FibonacciAir {};
    let mut sbuilder  = 
        SymbolicAirBuilder::<BabyBear, BabyBear, ()>::new(0, 2, 0, 0);
    air.eval(&mut sbuilder);
    sbuilder.print_lean_constraints();
}