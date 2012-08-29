#include "conditions/circe/parrain.h"
#include "pydata.h"
#include "stipulation/has_solution_type.h"
#include "stipulation/stipulation.h"
#include "stipulation/move_player.h"
#include "solving/move_effect_journal.h"
#include "debugging/trace.h"

#include <assert.h>
#include <stdlib.h>

static int move_vector(void)
{
  move_effect_journal_index_type const top = move_effect_journal_top[nbply];
  move_effect_journal_index_type curr;
  int result = 0;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  assert(move_effect_journal_top[nbply-1]<=top);

  for (curr = move_effect_journal_top[nbply-1]; curr!=top; ++curr)
    if (move_effect_journal[curr].type==move_effect_piece_movement)
    {
      square const from = move_effect_journal[curr].u.piece_movement.from;
      square const to = move_effect_journal[curr].u.piece_movement.to;
      result += to-from;
    }

  if (CondFlag[contraparrain])
    result = -result;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%d",result);
  TraceFunctionResultEnd();
  return result;
}

static void do_rebirth(void)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  if (pprise[parent_ply[nbply]]==vide)
    current_circe_rebirth_square[nbply] = initsquare;
  else
  {
    square const sq_capture = move_generation_stack[current_move[parent_ply[nbply]]].capture;

    current_circe_rebirth_square[nbply] = sq_capture+move_vector();

    if (e[current_circe_rebirth_square[nbply]]==vide)
    {
      ren_parrain[nbply] = pprise[parent_ply[nbply]];
      move_effect_journal_do_piece_addition(move_effect_reason_circe_rebirth,
                                            current_circe_rebirth_square[nbply],
                                            pprise[parent_ply[nbply]],
                                            pprispec[parent_ply[nbply]]);
    }
    else
      current_circe_rebirth_square[nbply] = initsquare;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Try to solve in n half-moves after a defense.
 * @param si slice index
 * @param n maximum number of half moves until goal
 * @return length of solution found and written, i.e.:
 *            slack_length-2 defense has turned out to be illegal
 *            <=n length of shortest solution found
 *            n+2 no solution found
 */
stip_length_type circe_parrain_rebirth_handler_attack(slice_index si,
                                                      stip_length_type n)
{
  stip_length_type result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParamListEnd();

  do_rebirth();
  result = attack(slices[si].next1,n);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Try to defend after an attacking move
 * When invoked with some n, the function assumes that the key doesn't
 * solve in less than n half moves.
 * @param si slice index
 * @param n maximum number of half moves until end state has to be reached
 * @return <slack_length - no legal defense found
 *         <=n solved  - <=acceptable number of refutations found
 *                       return value is maximum number of moves
 *                       (incl. defense) needed
 *         n+2 refuted - >acceptable number of refutations found
 */
stip_length_type circe_parrain_rebirth_handler_defend(slice_index si,
                                                      stip_length_type n)
{
  stip_length_type result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParamListEnd();

  do_rebirth();
  result = defend(slices[si].next1,n);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Instrument a stipulation
 * @param si identifies root slice of stipulation
 */
void stip_insert_circe_parrain_rebirth_handlers(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_instrument_moves_no_replay(si,STCirceParrainRebirthHandler);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}