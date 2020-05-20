#include "output/plaintext/line/refuting_variation_writer.h"
#include "stipulation/stipulation.h"
#include "stipulation/pipe.h"
#include "stipulation/branch.h"
#include "solving/machinery/solve.h"
#include "solving/ply.h"
#include "output/plaintext/protocol.h"
#include "output/plaintext/move_inversion_counter.h"
#include "output/plaintext/message.h"
#include "output/plaintext/tree/tree.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

/* Allocate a STOutputPlaintextLineRefutingVariationWriter slice.
 * @return index of allocated slice
 */
slice_index alloc_output_plaintext_line_refuting_variation_writer_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STOutputPlaintextLineRefutingVariationWriter);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Calculate the depth of a ply in the move tree
 * This is supposed to work robustly even in the presence of auxiliary plys
 * (e.g. for Take&Make).
 * @param p identifies the ply
 * @return p's depth
 */
static unsigned int depth(ply p)
{
  if (p<=ply_retro_move)
    return 0;
  else
    return depth(parent_ply[p])+1;
}

static void write_refuting_varation(unsigned move_depth)
{
  output_plaintext_tree_write_move();
  protocol_fputc(' ',stdout);
  output_plaintext_message(Refutation);
  output_plaintext_message(NewLine);
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
void output_plaintext_line_refuting_variation_writer_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  pipe_solve_delegate(si);

  if (solve_result_min()>MOVE_HAS_SOLVED_LENGTH())
  {
    unsigned int const move_depth = depth(nbply)+output_plaintext_nr_move_inversions;
    write_refuting_varation(move_depth);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
