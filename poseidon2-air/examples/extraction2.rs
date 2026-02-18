use p3_baby_bear::{BABYBEAR_RC24_EXTERNAL_FINAL, BABYBEAR_RC24_EXTERNAL_INITIAL, BABYBEAR_RC24_INTERNAL, BabyBear, GenericPoseidon2LinearLayersBabyBear};
// use p3_field::PrimeCharacteristicRing;
use p3_poseidon2_air::{Poseidon2Air, RoundConstants};
use p3_air::{Air, BaseAir, caching_symbolic_builder::CachingSymbolicAirBuilder, symbolic_builder::SymbolicAirBuilder};

pub fn main() {
    // let beginning_full_round_constants = [
    //     [BabyBear::from_i32(1774958255), BabyBear::from_i32(1185780729), BabyBear::from_i32(1621102414), BabyBear::from_i32(1796380621), BabyBear::from_i32(588815102), BabyBear::from_i32(1932426223), BabyBear::from_i32(1925334750), BabyBear::from_i32(747903232), BabyBear::from_i32(89648862), BabyBear::from_i32(360728943), BabyBear::from_i32(977184635), BabyBear::from_i32(1425273457), BabyBear::from_i32(256487465), BabyBear::from_i32(1200041953), BabyBear::from_i32(572403254), BabyBear::from_i32(448208942)],
    //     [BabyBear::from_i32(1215789478), BabyBear::from_i32(944884184), BabyBear::from_i32(953948096), BabyBear::from_i32(547326025), BabyBear::from_i32(646827752), BabyBear::from_i32(889997530), BabyBear::from_i32(1536873262), BabyBear::from_i32(86189867), BabyBear::from_i32(1065944411), BabyBear::from_i32(32019634), BabyBear::from_i32(333311454), BabyBear::from_i32(456061748), BabyBear::from_i32(1963448500), BabyBear::from_i32(1827584334), BabyBear::from_i32(1391160226), BabyBear::from_i32(1348741381)],
    //     [BabyBear::from_i32(88424255), BabyBear::from_i32(104111868), BabyBear::from_i32(1763866748), BabyBear::from_i32(79691676), BabyBear::from_i32(1988915530), BabyBear::from_i32(1050669594), BabyBear::from_i32(359890076), BabyBear::from_i32(573163527), BabyBear::from_i32(222820492), BabyBear::from_i32(159256268), BabyBear::from_i32(669703072), BabyBear::from_i32(763177444), BabyBear::from_i32(889367200), BabyBear::from_i32(256335831), BabyBear::from_i32(704371273), BabyBear::from_i32(25886717)],
    //     [BabyBear::from_i32(51754520), BabyBear::from_i32(1833211857), BabyBear::from_i32(454499742), BabyBear::from_i32(1384520381), BabyBear::from_i32(777848065), BabyBear::from_i32(1053320300), BabyBear::from_i32(1851729162), BabyBear::from_i32(344647910), BabyBear::from_i32(401996362), BabyBear::from_i32(1046925956), BabyBear::from_i32(5351995), BabyBear::from_i32(1212119315), BabyBear::from_i32(754867989), BabyBear::from_i32(36972490), BabyBear::from_i32(751272725), BabyBear::from_i32(506915399)],
    // ];
    // let ending_full_round_constants = [
    //     [BabyBear::from_i32(1922082829), BabyBear::from_i32(1870549801), BabyBear::from_i32(1502529704), BabyBear::from_i32(1990744480), BabyBear::from_i32(1700391016), BabyBear::from_i32(1702593455), BabyBear::from_i32(321330495), BabyBear::from_i32(528965731), BabyBear::from_i32(183414327), BabyBear::from_i32(1886297254), BabyBear::from_i32(1178602734), BabyBear::from_i32(1923111974), BabyBear::from_i32(744004766), BabyBear::from_i32(549271463), BabyBear::from_i32(1781349648), BabyBear::from_i32(542259047)],
    //     [BabyBear::from_i32(1536158148), BabyBear::from_i32(715456982), BabyBear::from_i32(503426110), BabyBear::from_i32(340311124), BabyBear::from_i32(1558555932), BabyBear::from_i32(1226350925), BabyBear::from_i32(742828095), BabyBear::from_i32(1338992758), BabyBear::from_i32(1641600456), BabyBear::from_i32(1843351545), BabyBear::from_i32(301835475), BabyBear::from_i32(43203215), BabyBear::from_i32(386838401), BabyBear::from_i32(1520185679), BabyBear::from_i32(1235297680), BabyBear::from_i32(904680097)],
    //     [BabyBear::from_i32(1491801617), BabyBear::from_i32(1581784677), BabyBear::from_i32(913384905), BabyBear::from_i32(247083962), BabyBear::from_i32(532844013), BabyBear::from_i32(107190701), BabyBear::from_i32(213827818), BabyBear::from_i32(1979521776), BabyBear::from_i32(1358282574), BabyBear::from_i32(1681743681), BabyBear::from_i32(1867507480), BabyBear::from_i32(1530706910), BabyBear::from_i32(507181886), BabyBear::from_i32(695185447), BabyBear::from_i32(1172395131), BabyBear::from_i32(1250800299)],
    //     [BabyBear::from_i32(1503161625), BabyBear::from_i32(817684387), BabyBear::from_i32(498481458), BabyBear::from_i32(494676004), BabyBear::from_i32(1404253825), BabyBear::from_i32(108246855), BabyBear::from_i32(59414691), BabyBear::from_i32(744214112), BabyBear::from_i32(890862029), BabyBear::from_i32(1342765939), BabyBear::from_i32(1417398904), BabyBear::from_i32(1897591937), BabyBear::from_i32(1066647396), BabyBear::from_i32(1682806907), BabyBear::from_i32(1015795079), BabyBear::from_i32(1619482808)],
    // ];

    // let partial_round_constants = [
    //     BabyBear::from_i32(1518359488),
    //     BabyBear::from_i32(1765533241),
    //     BabyBear::from_i32(945325693),
    //     BabyBear::from_i32(422793067),
    //     BabyBear::from_i32(311365592),
    //     BabyBear::from_i32(1311448267),
    //     BabyBear::from_i32(1629555936),
    //     BabyBear::from_i32(1009879353),
    //     BabyBear::from_i32(190525218),
    //     BabyBear::from_i32(786108885),
    //     BabyBear::from_i32(557776863),
    //     BabyBear::from_i32(212616710),
    //     BabyBear::from_i32(605745517)
    // ];

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

// LinearLayers::external_linear_layer - 0 constraints

// eval_sbox (7,1) - 1 constraint

// eval_full_round (2*WIDTH) constraints
// - WIDTH calls to eval_sbox - WIDTH constraints
// - external_linear_layer - 0 constraints
// - WIDTH constraints

// first half full rounds 2*WIDTH*HALF_FULL_ROUNDS constraints
// - HALF FULL ROUNDS calls to eval_full_round

// eval_partial_round - 2 constraints
// - eval_sbox - 1 constraint
// - 1 constraint

// partial rounds - 2 * PARTIAL_ROUNDS constraints

// second half full rounds 2*WIDTH*HALF_FULL_ROUNDS constraints

// WIDTH=16
// HALF_FULL_ROUNDS = 4
// PARTIAL_ROUNDS = 13
// total constraints = 2*16*4 + 2*13 + 2*16*4 = 282 - correct

// constraint breakdown
// 0-31 - full round 1
// 32-63 - full round 2
// 64-95 - full round 3
// 96-127 - full round 4
// 128-153 - partial rounds (in sequential pairs)
// 154-185 - full round 5
// 186-217 - full round 6
// 218-249 - full round 7
// 250-281 - full round 8
