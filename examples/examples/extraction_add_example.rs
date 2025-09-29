use p3_baby_bear::BabyBear;
use p3_field::*;
use p3_matrix::Matrix;

use p3_air::{
    Air, AirBuilder, BaseAir, symbolic_builder::SymbolicAirBuilder,
};

pub struct Add8Air {}

// a, b, c, r, c₀, c₁, c₂, ... c₇
const NUM_ADD_COLS: usize = 12;

impl<F> BaseAir<F> for Add8Air {
    fn width(&self) -> usize {
        NUM_ADD_COLS
    }
}

impl<AB: AirBuilder> Air<AB> for Add8Air {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0).expect("Matrix is empty?");

        let pow_of_2 = (0..=8).map(|i| AB::F::from_u64(1 << i)).collect::<Vec<_>>();
        // a + b = 2^8 * r + c
        builder.assert_eq(
            local[0].clone() + local[1].clone(), 
            (local[3].clone() * pow_of_2[8].clone()) + local[2].clone()
        );

        // r^2 - r = 0
        builder.assert_eq(
            (local[3].clone()) * (local[3].clone()), 
            (local[3].clone()).into()
        );

        // c = c₁ + 2*c₂ + 4*c₃ + ... + 128 * c₇
        builder.assert_eq(
            (local[2].clone()).into(),
            local[4..12]
                .iter()
                .enumerate()
                .map(|(i, cell)| cell.clone() * pow_of_2[i].clone())
                .sum::<AB::Expr>(),
        );

        // ∀ i, cᵢ² - cᵢ = 0
        for c in &local[4..12] {
            builder.assert_eq(
                c.clone() * c.clone(), 
                c.clone().into()
            );
        }
    }
}

pub fn main() {
    let air = Add8Air {};
    let mut sbuilder = SymbolicAirBuilder::<BabyBear, BabyBear, ()>::new(0, NUM_ADD_COLS, 0, 0);
    air.eval(&mut sbuilder);
    sbuilder.print_lean_constraints();
}

#[test]
pub fn extract_fib() {
    main()
}
