#include "solving/non_king_move_generator.h"
#include "solving/move_generator.h"
#include "stipulation/stipulation.h"
#include "solving/has_solution_type.h"
#include "stipulation/pipe.h"
#include "solving/temporary_hacks.h"
#include "position/position.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

#include "debugging/assert.h"

/* Allocate a STNonKingMoveGenerator slice.
 * @return index of allocated slice
 */
slice_index alloc_non_king_move_generator_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STNonKingMoveGenerator);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

static boolean advance_departure_square(Side side,
                                        square const **next_square_to_try)
{
  while (true)
  {
    curr_generation->departure = **next_square_to_try;
    if (curr_generation->departure==0)
      break;
    else
    {
      ++*next_square_to_try;
      if (TSTFLAG(spec[curr_generation->departure],side)
          /* don't use king_square[side] - it may be a royal square occupied
           * by a non-royal piece! */
          && !TSTFLAG(spec[curr_generation->departure],Royal))
      {
        move_generation_current_walk = get_walk_of_piece_on_square(curr_generation->departure);
        solve(slices[temporary_hack_move_generator[side]].next2);
        return true;
      }
    }
  }

  return false;
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
void non_king_move_generator_solve(slice_index si)
{
  Side const side_at_move = slices[si].starter;
  square const *next_square_to_try = boardnum;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  solve_result = immobility_on_next_move;

  nextply(side_at_move);

  while (solve_result<slack_length
         && advance_departure_square(side_at_move,&next_square_to_try))
    pipe_solve_delegate(si);

  finply();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
