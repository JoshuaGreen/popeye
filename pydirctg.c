#include "pydirctg.h"
#include "stipulation/proxy.h"
#include "stipulation/goals/goals.h"
#include "stipulation/branch.h"
#include "stipulation/battle_play/branch.h"
#include "stipulation/battle_play/attack_adapter.h"
#include "stipulation/battle_play/ready_for_attack.h"
#include "stipulation/battle_play/attack_move_to_goal.h"
#include "stipulation/battle_play/attack_fork.h"
#include "stipulation/battle_play/defense_adapter.h"
#include "trace.h"

#include <assert.h>

/* Instrument a branch with slices dealing with direct play
 * @param si root of branch to be instrumented
 * @param proxy_to_goal identifies slice leading towards goal
 */
void slice_insert_direct_guards(slice_index si, slice_index proxy_to_goal)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",proxy_to_goal);
  TraceFunctionParamListEnd();

  TraceStipulation(si);
  TraceStipulation(proxy_to_goal);

  assert(slices[proxy_to_goal].type==STProxy);

  {
    SliceType const types_to_be_removed[] =
    {
      STAttackAdapter,
      STReadyForAttack
    };
    enum
    {
      nr_types_to_be_removed = (sizeof types_to_be_removed
                                / sizeof types_to_be_removed[0])
    };
    battle_branch_remove_slices(proxy_to_goal,
                                types_to_be_removed,nr_types_to_be_removed);
  }

  {
    slice_index const prototype = alloc_attack_fork_slice(proxy_to_goal);
    battle_branch_insert_slices(si,&prototype,1);
  }

  TraceStipulation(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Insert a the appropriate proxy slices before each STGoal*ReachedTester slice
 * @param si identifies STGoal*ReachedTester slice
 * @param st address of structure representing the traversal
 */
static void instrument_testing(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children(si,st);

  {
    slice_index const adapter = alloc_attack_adapter_slice(slack_length_battle+1,
                                                           slack_length_battle);
    Goal const goal = slices[si].u.goal_writer.goal;
    slice_index const prototypes[] =
    {
      alloc_ready_for_attack_slice(slack_length_battle+1,slack_length_battle),
      alloc_attack_move_to_goal_slice(goal),
      alloc_pipe(STAttackMoveShoeHorningDone),
      alloc_pipe(STAttackMoveLegalityChecked),
      alloc_defense_adapter_slice(slack_length_battle+1,slack_length_battle)
    };
    enum {
      nr_prototypes = sizeof prototypes / sizeof prototypes[0]
    };
    pipe_append(slices[si].prev,adapter);
    battle_branch_insert_slices(adapter,prototypes,nr_prototypes);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Instrument a branch leading to a goal to be a direct goal branch
 * @param si identifies entry slice of branch
 */
void slice_make_direct_goal_branch(slice_index si)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  stip_structure_traversal_init(&st,0);
  stip_structure_traversal_override_single(&st,
                                           STGoalReachedTesting,
                                           &instrument_testing);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
