use p3_baby_bear::BabyBear;
use p3_field::*;
use p3_matrix::Matrix;

use crate::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, air, symbolic_builder::SymbolicAirBuilder,
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

        let local = 
            main.row_slice(0).expect("Matrix is empty?");

        // a + b = c + 2^8 * r
        builder.assert_eq::<<AB as air::AirBuilder>::Expr, <AB as air::AirBuilder>::Expr>(
            local[0] + local[1],
            (<AB as air::AirBuilder>::Expr::from(local[3]) * AB::F::from_u32(256)) + local[2],
        );

        // r^2 - r = 0 
        builder.assert_eq::<<AB as air::AirBuilder>::Expr, <AB as air::AirBuilder>::Expr>(
            <AB as air::AirBuilder>::Expr::from(local[3]) * <AB as air::AirBuilder>::Expr::from(local[3]),
            <AB as air::AirBuilder>::Expr::from(local[3]) 
        );
        
        // c = c₁ + 2*c₂ + 4*c₃ + ... + 128 * c₇
        builder.assert_eq::<<AB as air::AirBuilder>::Expr, <AB as air::AirBuilder>::Expr>(
            <AB as air::AirBuilder>::Expr::from(local[2]),
            <AB as air::AirBuilder>::Expr::from(local[4]) +  
            <AB as air::AirBuilder>::Expr::from(local[5]) * AB::F::from_u32(2) +  
            <AB as air::AirBuilder>::Expr::from(local[6]) * AB::F::from_u32(4) +
            <AB as air::AirBuilder>::Expr::from(local[7]) * AB::F::from_u32(8) +
            <AB as air::AirBuilder>::Expr::from(local[8]) * AB::F::from_u32(16) +
            <AB as air::AirBuilder>::Expr::from(local[9]) * AB::F::from_u32(32) +
            <AB as air::AirBuilder>::Expr::from(local[10]) * AB::F::from_u32(64) +
            <AB as air::AirBuilder>::Expr::from(local[11]) * AB::F::from_u32(128)
        );

        // ∀ i, cᵢ² - cᵢ = 0 
        for i in 0..8 {
            builder.assert_eq::<<AB as air::AirBuilder>::Expr, <AB as air::AirBuilder>::Expr>(
                <AB as air::AirBuilder>::Expr::from(local[4 + i]) * <AB as air::AirBuilder>::Expr::from(local[4 + i]),
                <AB as air::AirBuilder>::Expr::from(local[4 + i])
            );
        }

    }
}

#[test]
fn extract_fib() {
    let air = Add8Air {};
    let mut sbuilder = SymbolicAirBuilder::<BabyBear, BabyBear, ()>::new(0, 2, 0, 0);
    air.eval(&mut sbuilder);
    sbuilder.print_lean_constraints();
}

