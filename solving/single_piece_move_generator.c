#include "solving/single_piece_move_generator.h"
#include "position/position.h"
#include "solving/move_generator.h"
#include "stipulation/stipulation.h"
#include "stipulation/pipe.h"
#include "solving/temporary_hacks.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

#include "debugging/assert.h"

static square square_departure;

void init_single_piece_move_generator(square sq_departure)
{
  TraceFunctionEntry(__func__);
  TraceSquare(sq_departure);
  TraceFunctionParamListEnd();

  assert(square_departure==initsquare);
  square_departure = sq_departure;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Allocate a STSinglePieceMoveGenerator slice.
 * @return index of allocated slice
 */
slice_index alloc_single_piece_move_generator_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STSinglePieceMoveGenerator);

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
void single_piece_move_generator_solve(slice_index si)
{
  Side const side_at_move = slices[si].starter;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  nextply(side_at_move);

  curr_generation->departure = square_departure;
  move_generation_current_walk = get_walk_of_piece_on_square(curr_generation->departure);
  generate_moves_for_piece(slices[temporary_hack_move_generator[side_at_move]].next2);

  square_departure = initsquare;

  pipe_solve_delegate(si);

  finply();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
