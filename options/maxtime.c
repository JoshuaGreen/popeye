#include "options/maxtime.h"
#include "stipulation/pipe.h"
#include "platform/maxtime.h"
#include "stipulation/battle_play/branch.h"
#include "stipulation/help_play/branch.h"
#include "solving/pipe.h"
#include "output/plaintext/message.h"
#include "debugging/trace.h"
#include "debugging/assert.h"

/* Allocate a STMaxTimeGuard slice.
 * @return allocated slice
 */
static slice_index alloc_maxtime_guard(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STMaxTimeGuard);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Try to solve in solve_nr_remaining half-moves.
 * @param si slice index
 * @note assigns solve_result the length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played is illegal
 *            this_move_is_illegal     the move being played is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 *            (with n denominating solve_nr_remaining)
 */
void maxtime_guard_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  pipe_this_move_doesnt_solve_if(si,hasMaxtimeElapsed());

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Try to solve in solve_nr_remaining half-moves.
 * @param si slice index
 * @note assigns solve_result the length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played is illegal
 *            this_move_is_illegal     the move being played is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 *            (with n denominating solve_nr_remaining)
 */
void maxtime_set(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (dealWithMaxtime())
  {
    pipe_solve_delegate(si);
    resetMaxtimeTimer();
  }
  else
  {
    output_plaintext_verifie_message(NoMaxTime);
    pipe_solve_delegate(si);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Insert a STMaxTimeGuard slice after a STHelpMove slice
 */
static void insert_maxtime_help_guard(slice_index si,
                                      stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  {
    slice_index const prototype = alloc_maxtime_guard();
    help_branch_insert_slices(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_maxtime_defender_guard(slice_index si,
                                          stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  {
    slice_index const prototype = alloc_maxtime_guard();
    attack_branch_insert_slices(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor maxtime_guard_inserters[] =
{
  { STReadyForHelpMove, &insert_maxtime_help_guard     },
  { STReadyForAttack,   &insert_maxtime_defender_guard }
};
enum
{
  nr_maxtime_guard_inserters = (sizeof maxtime_guard_inserters
                                / sizeof maxtime_guard_inserters[0])
};

/* Instrument a stipulation with STMaxTimeGuard slices
 * @param si identifies slice where to start
 */
void solving_insert_maxtime_guards(slice_index si)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  stip_structure_traversal_init(&st,0);
  stip_structure_traversal_override_by_function(&st,
                                                slice_function_conditional_pipe,
                                                &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override(&st,
                                    maxtime_guard_inserters,
                                    nr_maxtime_guard_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
