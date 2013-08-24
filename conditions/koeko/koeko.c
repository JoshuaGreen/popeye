#include "conditions/koeko/koeko.h"
#include "solving/move_effect_journal.h"
#include "solving/observation.h"
#include "stipulation/has_solution_type.h"
#include "stipulation/stipulation.h"
#include "stipulation/move.h"
#include "stipulation/temporary_hacks.h"
#include "debugging/trace.h"

nocontactfunc_t koeko_nocontact;

/* Try to solve in n half-moves.
 * @param si slice index
 * @param n maximum number of half moves
 * @return length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played (or being played)
 *                                     is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 */
stip_length_type koeko_legality_tester_solve(slice_index si,
                                                  stip_length_type n)
{
  stip_length_type result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParamListEnd();

  {
    move_effect_journal_index_type const base = move_effect_journal_base[nbply];
    move_effect_journal_index_type const movement = base+move_effect_journal_index_offset_movement;
    square const sq_arrival = move_effect_journal[movement].u.piece_movement.to;
    PieceIdType const moving_id = GetPieceId(move_effect_journal[movement].u.piece_movement.movingspec);
    square const pos = move_effect_journal_follow_piece_through_other_effects(nbply,
                                                                              moving_id,
                                                                              sq_arrival);
    if ((*koeko_nocontact)(pos))
      result = previous_move_is_illegal;
    else
      result = solve(slices[si].next1,n);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Initialise solving in Koeko
 * @param si identifies the root slice of the stipulation
 */
void koeko_initialise_solving(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  stip_instrument_moves(si,STKoekoLegalityTester);

  observation_play_move_to_validate(si,nr_sides);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static boolean noleapcontact(square sq_arrival, vec_index_type kanf, vec_index_type kend)
{
  boolean result = true;
  vec_index_type k;

  TraceFunctionEntry(__func__);
  TraceSquare(sq_arrival);
  TraceFunctionParamListEnd();

  for (k = kanf; k<=kend; ++k)
  {
    square const sq_candidate = sq_arrival+vec[k];
    if (!is_square_empty(sq_candidate) && !is_square_blocked(sq_candidate))
    {
      result = false;
      break;
    }
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

boolean nokingcontact(square ia)
{
  return noleapcontact(ia, vec_queen_start, vec_queen_end);
}

boolean nowazircontact(square ia)
{
  return noleapcontact(ia, vec_rook_start, vec_rook_end);
}

boolean noferscontact(square ia)
{
  return noleapcontact(ia, vec_bishop_start, vec_bishop_end);
}

boolean noknightcontact(square ia)
{
  return noleapcontact(ia, vec_knight_start, vec_knight_end);
}

boolean nocamelcontact(square ia)
{
  return noleapcontact(ia, vec_chameau_start, vec_chameau_end);
}

boolean noalfilcontact(square ia)
{
  return noleapcontact(ia, vec_alfil_start, vec_alfil_end);
}

boolean nodabbabacontact(square ia)
{
  return noleapcontact(ia, vec_dabbaba_start, vec_dabbaba_end);
}

boolean nozebracontact(square ia)
{
  return noleapcontact(ia, vec_zebre_start, vec_zebre_end);
}

boolean nogiraffecontact(square ia)
{
  return noleapcontact(ia, vec_girafe_start, vec_girafe_end);
}

boolean noantelopecontact(square ia)
{
  return noleapcontact(ia, vec_antilope_start, vec_antilope_end);
}
