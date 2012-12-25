#include "stipulation/temporary_hacks.h"
#include "stipulation/pipe.h"
#include "stipulation/has_solution_type.h"
#include "stipulation/branch.h"
#include "stipulation/proxy.h"
#include "stipulation/end_of_branch.h"
#include "stipulation/conditional_pipe.h"
#include "stipulation/move_inverter.h"
#include "stipulation/boolean/true.h"
#include "stipulation/boolean/not.h"
#include "stipulation/goals/reached_tester.h"
#include "stipulation/goals/mate/reached_tester.h"
#include "stipulation/goals/immobile/reached_tester.h"
#include "stipulation/goals/any/reached_tester.h"
#include "stipulation/goals/capture/reached_tester.h"
#include "stipulation/battle_play/branch.h"
#include "stipulation/help_play/branch.h"
#include "solving/legal_move_counter.h"
#include "conditions/sat.h"
#include "optimisations/count_nr_opponent_moves/opponent_moves_counter.h"
#include "debugging/trace.h"

#include <assert.h>

slice_index temporary_hack_mate_tester[nr_sides];
slice_index temporary_hack_immobility_tester[nr_sides];
slice_index temporary_hack_exclusive_mating_move_counter[nr_sides];
slice_index temporary_hack_brunner_check_defense_finder[nr_sides];
slice_index temporary_hack_ultra_mummer_length_measurer[nr_sides];
slice_index temporary_hack_king_capture_legality_tester[nr_sides];
slice_index temporary_hack_cagecirce_noncapture_finder[nr_sides];
slice_index temporary_hack_circe_take_make_rebirth_squares_finder[nr_sides];
slice_index temporary_hack_castling_intermediate_move_legality_tester[nr_sides];
slice_index temporary_hack_opponent_moves_counter[nr_sides];
slice_index temporary_hack_sat_flights_counter[nr_sides];

static slice_index make_mate_tester_fork(Side side)
{
  Goal const mate_goal = { goal_mate, initsquare };
  slice_index const mate_tester = alloc_goal_mate_reached_tester_system();
  slice_index const result = alloc_goal_reached_tester_slice(mate_goal,mate_tester);
  dealloc_slice(slices[result].next1);
  stip_impose_starter(result,side);
  return result;
}

static slice_index make_exclusive_mating_move_counter_fork(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const proxy_to_goal = alloc_proxy_slice();
  Goal const goal = { goal_mate, initsquare };
  slice_index const tester_system = alloc_goal_mate_reached_tester_system();
  slice_index const tester_slice = alloc_goal_reached_tester_slice(goal,tester_system);
  slice_index const attack = alloc_battle_branch(slack_length+1,slack_length+1);
  slice_index const counter_proto = alloc_legal_attack_counter_slice();
  slice_index const unsuspender_proto = alloc_pipe(STExclusiveChessUnsuspender);
  attack_branch_insert_slices(tester_slice,&counter_proto,1);
  link_to_branch(proxy_to_goal,tester_slice);
  link_to_branch(proxy_branch,attack);
  battle_branch_insert_direct_end_of_branch_goal(attack,proxy_to_goal);
  branch_insert_slices(attack,&unsuspender_proto,1);
  result = alloc_conditional_pipe(STExclusiveChessMatingMoveCounter,proxy_branch);
  stip_impose_starter(result,side);
  return result;
}

static slice_index make_immobility_tester_fork(Side side)
{
  slice_index const result = alloc_goal_immobile_reached_tester_slice(goal_applies_to_starter);
  stip_impose_starter(result,side);
  return result;
}

static slice_index make_brunner_check_defense_finder(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const help = alloc_help_branch(slack_length+1,slack_length+1);
  slice_index const proxy_goal = alloc_proxy_slice();
  slice_index const system = alloc_goal_any_reached_tester_system();
  link_to_branch(proxy_goal,system);
  help_branch_set_end_goal(help,proxy_goal,1);
  link_to_branch(proxy_branch,help);
  result = alloc_conditional_pipe(STBrunnerDefenderFinder,proxy_branch);
  stip_impose_starter(result,side);
  return result;
}

static slice_index make_king_capture_legality_tester(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const help = alloc_help_branch(slack_length+1,slack_length+1);
  slice_index const proxy_goal = alloc_proxy_slice();
  slice_index const system = alloc_goal_any_reached_tester_system();
  link_to_branch(proxy_goal,system);
  help_branch_set_end_goal(help,proxy_goal,1);
  link_to_branch(proxy_branch,help);
  result = alloc_conditional_pipe(STKingCaptureLegalityTester,proxy_branch);
  stip_impose_starter(result,side);
  return result;
}

static slice_index make_ultra_mummer_length_measurer(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const help = alloc_help_branch(slack_length+1,slack_length+1);
  slice_index const proxy_goal = alloc_proxy_slice();
  slice_index const system = alloc_goal_any_reached_tester_system();
  link_to_branch(proxy_goal,system);
  help_branch_set_end_goal(help,proxy_goal,1);
  link_to_branch(proxy_branch,help);
  result = alloc_conditional_pipe(STUltraMummerMeasurerFork,proxy_branch);
  stip_impose_starter(result,side);
  return result;
}

static slice_index make_cagecirce_noncapture_finder(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const help = alloc_help_branch(slack_length+1,slack_length+1);
  slice_index const proxy_goal = alloc_proxy_slice();
  slice_index const system = alloc_goal_capture_reached_tester_system();
  link_to_branch(proxy_goal,system);

  {
    slice_index const tester = branch_find_slice(STGoalReachedTester,
                                                 proxy_goal,
                                                 stip_traversal_context_intro);
    assert(tester!=no_slice);
    pipe_append(slices[tester].next2,alloc_not_slice());
    slices[tester].u.goal_handler.goal.type = goal_negated;
    help_branch_set_end_goal(help,proxy_goal,1);
    link_to_branch(proxy_branch,help);
    result = alloc_conditional_pipe(STCageCirceNonCapturingMoveFinder,proxy_branch);
    stip_impose_starter(result,side);
  }

  return result;
}

static slice_index make_circe_take_make_rebirth_squares_finder(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const help = alloc_help_branch(slack_length+1,slack_length+1);
  slice_index const prototype = alloc_pipe(STTakeMakeCirceCollectRebirthSquares);
  link_to_branch(proxy_branch,help);
  help_branch_insert_slices(help,&prototype,1);
  result = alloc_conditional_pipe(STTakeMakeCirceCollectRebirthSquaresFork,proxy_branch);
  stip_impose_starter(result,side);

  return result;
}

static slice_index make_castling_intermediate_move_legality_tester(Side side)
{
  slice_index result;
  slice_index const proxy_branch = alloc_proxy_slice();
  slice_index const help = alloc_help_branch(slack_length+1,slack_length+1);
  slice_index const proxy_goal = alloc_proxy_slice();
  slice_index const system = alloc_goal_any_reached_tester_system();
  link_to_branch(proxy_goal,system);
  help_branch_set_end_goal(help,proxy_goal,1);
  link_to_branch(proxy_branch,help);
  result = alloc_conditional_pipe(STCastlingIntermediateMoveLegalityTester,proxy_branch);
  stip_impose_starter(result,side);

  return result;
}

static slice_index make_opponent_moves_counter_fork(Side side)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceEnumerator(Side,side,"");
  TraceFunctionParamListEnd();

  {
    slice_index const proxy = alloc_proxy_slice();
    slice_index const prototypes[] =
    {
        alloc_pipe(STOpponentMovesCounter),
        alloc_legal_attack_counter_slice()
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    slice_index const attack = alloc_defense_branch(slack_length+2,slack_length+1);
    branch_insert_slices(attack,prototypes,nr_prototypes);
    link_to_branch(proxy,attack);
    result = alloc_conditional_pipe(STOpponentMovesCounterFork,proxy);
    stip_impose_starter(result,side);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

static slice_index make_sat_flights_counter(Side side)
{
  slice_index const proxy = alloc_proxy_slice();
  slice_index const result = alloc_conditional_pipe(STSATFlightsCounterFork,proxy);
  slice_index const legal_moves_counter = alloc_legal_defense_counter_slice();
  slice_index const defense = alloc_defense_branch(slack_length+1,slack_length+1);
  branch_insert_slices(defense,&legal_moves_counter,1);
  link_to_branch(proxy,defense);
  stip_impose_starter(result,side);
  return result;
}

void insert_temporary_hacks(slice_index root_slice)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",root_slice);
  TraceFunctionParamListEnd();

  {
    slice_index const proxy = alloc_proxy_slice();
    slice_index const entry_point = alloc_conditional_pipe(STTemporaryHackFork,proxy);

    slice_index const inverter = alloc_move_inverter_slice();

    pipe_link(proxy,alloc_true_slice());

    temporary_hack_mate_tester[Black] = make_mate_tester_fork(Black);
    temporary_hack_mate_tester[White] = make_mate_tester_fork(White);

    temporary_hack_immobility_tester[Black] = make_immobility_tester_fork(Black);
    temporary_hack_immobility_tester[White] = make_immobility_tester_fork(White);

    temporary_hack_exclusive_mating_move_counter[Black] = make_exclusive_mating_move_counter_fork(Black);
    temporary_hack_exclusive_mating_move_counter[White] = make_exclusive_mating_move_counter_fork(White);

    temporary_hack_brunner_check_defense_finder[Black] = make_brunner_check_defense_finder(Black);
    temporary_hack_brunner_check_defense_finder[White] = make_brunner_check_defense_finder(White);

    temporary_hack_ultra_mummer_length_measurer[Black] = make_ultra_mummer_length_measurer(Black);
    temporary_hack_ultra_mummer_length_measurer[White] = make_ultra_mummer_length_measurer(White);

    temporary_hack_king_capture_legality_tester[Black] = make_king_capture_legality_tester(Black);
    temporary_hack_king_capture_legality_tester[White] = make_king_capture_legality_tester(White);

    temporary_hack_cagecirce_noncapture_finder[Black] = make_cagecirce_noncapture_finder(Black);
    temporary_hack_cagecirce_noncapture_finder[White] = make_cagecirce_noncapture_finder(White);

    temporary_hack_circe_take_make_rebirth_squares_finder[Black] = make_circe_take_make_rebirth_squares_finder(Black);
    temporary_hack_circe_take_make_rebirth_squares_finder[White] = make_circe_take_make_rebirth_squares_finder(White);

    temporary_hack_castling_intermediate_move_legality_tester[Black] = make_castling_intermediate_move_legality_tester(Black);
    temporary_hack_castling_intermediate_move_legality_tester[White] = make_castling_intermediate_move_legality_tester(White);

    temporary_hack_opponent_moves_counter[Black] = make_opponent_moves_counter_fork(Black);
    temporary_hack_opponent_moves_counter[White] = make_opponent_moves_counter_fork(White);

    temporary_hack_sat_flights_counter[Black] = make_sat_flights_counter(Black);
    temporary_hack_sat_flights_counter[White] = make_sat_flights_counter(White);

    pipe_append(root_slice,entry_point);

    pipe_append(proxy,temporary_hack_mate_tester[White]);
    pipe_append(temporary_hack_mate_tester[White],
                temporary_hack_immobility_tester[White]);
    pipe_append(temporary_hack_immobility_tester[White],
                temporary_hack_exclusive_mating_move_counter[White]);
    pipe_append(temporary_hack_exclusive_mating_move_counter[White],
                temporary_hack_brunner_check_defense_finder[White]);
    pipe_append(temporary_hack_brunner_check_defense_finder[White],
                temporary_hack_ultra_mummer_length_measurer[White]);
    pipe_append(temporary_hack_ultra_mummer_length_measurer[White],
                temporary_hack_king_capture_legality_tester[White]);
    pipe_append(temporary_hack_king_capture_legality_tester[White],
                temporary_hack_cagecirce_noncapture_finder[White]);
    pipe_append(temporary_hack_cagecirce_noncapture_finder[White],
                temporary_hack_circe_take_make_rebirth_squares_finder[White]);
    pipe_append(temporary_hack_circe_take_make_rebirth_squares_finder[White],
                temporary_hack_castling_intermediate_move_legality_tester[White]);
    pipe_append(temporary_hack_castling_intermediate_move_legality_tester[White],
                temporary_hack_opponent_moves_counter[White]);
    pipe_append(temporary_hack_opponent_moves_counter[White],
                temporary_hack_sat_flights_counter[White]);
    pipe_append(temporary_hack_sat_flights_counter[White],
                inverter);

    pipe_append(inverter,temporary_hack_mate_tester[Black]);
    pipe_append(temporary_hack_mate_tester[Black],
                temporary_hack_immobility_tester[Black]);
    pipe_append(temporary_hack_immobility_tester[Black],
                temporary_hack_exclusive_mating_move_counter[Black]);
    pipe_append(temporary_hack_exclusive_mating_move_counter[Black],
                temporary_hack_brunner_check_defense_finder[Black]);
    pipe_append(temporary_hack_brunner_check_defense_finder[Black],
                temporary_hack_ultra_mummer_length_measurer[Black]);
    pipe_append(temporary_hack_ultra_mummer_length_measurer[Black],
                temporary_hack_king_capture_legality_tester[Black]);
    pipe_append(temporary_hack_king_capture_legality_tester[Black],
                temporary_hack_cagecirce_noncapture_finder[Black]);
    pipe_append(temporary_hack_cagecirce_noncapture_finder[Black],
                temporary_hack_circe_take_make_rebirth_squares_finder[Black]);
    pipe_append(temporary_hack_circe_take_make_rebirth_squares_finder[Black],
                temporary_hack_castling_intermediate_move_legality_tester[Black]);
    pipe_append(temporary_hack_castling_intermediate_move_legality_tester[Black],
                temporary_hack_opponent_moves_counter[Black]);
    pipe_append(temporary_hack_opponent_moves_counter[Black],
                temporary_hack_sat_flights_counter[Black]);

    if (slices[root_slice].starter==Black)
      pipe_append(proxy,alloc_move_inverter_slice());
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
