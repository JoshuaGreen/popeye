#include "solving/find_move.h"
#include "solving/move_generator.h"
#include "stipulation/stipulation.h"
#include "stipulation/pipe.h"
#include "solving/machinery/slack_length.h"
#include "solving/has_solution_type.h"
#include "solving/post_move_iteration.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

#include "debugging/assert.h"

/* Allocate a STFindAttack slice.
 * @return index of allocated slice
 */
slice_index alloc_find_attack_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STFindAttack);

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
void find_attack_solve(slice_index si)
{
  stip_length_type result_intermediate_min = MOVE_HAS_NOT_SOLVED_LENGTH();
  stip_length_type result_intermediate_max = MOVE_HAS_NOT_SOLVED_LENGTH();

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  while (encore() && result_intermediate_max>MOVE_HAS_SOLVED_LENGTH())
  {
    pipe_solve_delegate(si);
    stip_length_type const solve_result_minimum = solve_result_min();
    stip_length_type const solve_result_maximum = solve_result_min();
    assert(slack_length<=solve_result_maximum || solve_result_minimum<=immobility_on_next_move);
    if (slack_length<solve_result_minimum)
    {
      if (solve_result_minimum<result_intermediate_min)
        result_intermediate_min = solve_result_minimum;
      if (solve_result_maximum<result_intermediate_max)
        result_intermediate_max = solve_result_maximum;
    }
  }

  set_solve_result_range(result_intermediate_min, result_intermediate_max);

  if (encore())
    post_move_iteration_cancel();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Continue determining whether a side is in check
 * @param si identifies the check tester
 * @param side_in_check which side?
 * @return true iff side_in_check is in check according to slice si
 */
boolean find_attack_is_in_check(slice_index si, Side side_observed)
{
  boolean result = false;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceEnumerator(Side,side_observed);
  TraceFunctionParamListEnd();

  while (encore())
    if (pipe_is_in_check_recursive_delegate(si,side_observed))
    {
      result = true;
      break;
    }
    else
      --CURRMOVE_OF_PLY(nbply);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Allocate a STFindDefense slice.
 * @return index of allocated slice
 */
slice_index alloc_find_defense_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STFindDefense);

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
void find_defense_solve(slice_index si)
{
  stip_length_type result_intermediate_min = immobility_on_next_move;
  stip_length_type result_intermediate_max = immobility_on_next_move;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  while (result_intermediate_min<=MOVE_HAS_SOLVED_LENGTH() && encore())
  {
    pipe_solve_delegate(si);

    stip_length_type solve_result_m = solve_result_max();
    assert(slack_length<=solve_result_m || solve_result_might_equal(this_move_is_illegal));
    if (result_intermediate_max<solve_result_m)
      result_intermediate_max = solve_result_m;
    solve_result_m = solve_result_min();
    if (result_intermediate_min<solve_result_m)
      result_intermediate_min = solve_result_m;
  }

  set_solve_result_range(result_intermediate_min, result_intermediate_max);

  if (encore())
    post_move_iteration_cancel();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
