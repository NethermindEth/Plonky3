use p3_baby_bear::{BABYBEAR_RC24_EXTERNAL_FINAL, BABYBEAR_RC24_EXTERNAL_INITIAL, BABYBEAR_RC24_INTERNAL, BabyBear, GenericPoseidon2LinearLayersBabyBear};
use p3_poseidon2_air::{Poseidon2Air, RoundConstants};
use p3_air::{Air, BaseAir, caching_symbolic_builder::CachingSymbolicAirBuilder, symbolic_builder::SymbolicAirBuilder};

pub fn main() {

    let constants: RoundConstants<BabyBear, 24, 4, 21> = RoundConstants::new(
        BABYBEAR_RC24_EXTERNAL_INITIAL, //beginning_full_round_constants, 
        BABYBEAR_RC24_INTERNAL, //partial_round_constants,
        BABYBEAR_RC24_EXTERNAL_FINAL, //ending_full_round_constants
    );
    println!("Constants: {constants:?}");
    let air: Poseidon2Air<
        BabyBear,
        GenericPoseidon2LinearLayersBabyBear,
        24,
        11,
        2,
        4,
        21
    > = Poseidon2Air::new(
        constants
    );

    println!("Width: {}", air.width());




    let mut sbuilder = CachingSymbolicAirBuilder::<BabyBear, BabyBear>::new(
        0,
        air.width(),
        0,
        0,
        0
    );
    air.eval(&mut sbuilder);
    sbuilder.print_lean_constraints();
}
