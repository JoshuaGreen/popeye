#include "conditions/sentinelles.h"
#include "pieces/attributes/neutral/neutral.h"
#include "pieces/walks/classification.h"
#include "stipulation/stipulation.h"
#include "stipulation/move.h"
#include "stipulation/has_solution_type.h"
#include "solving/move_effect_journal.h"
#include "debugging/trace.h"
#include "pieces/pieces.h"

#include <assert.h>

unsigned int sentinelles_max_nr_pawns[nr_sides];
unsigned int sentinelles_max_nr_pawns_total;

PieNam sentinelle;

boolean SentPionAdverse;
boolean SentPionNeutral;
boolean flagparasent;

static void insert_sentinelle(Side trait_ply)
{
  move_effect_journal_index_type const top = move_effect_journal_base[nbply];
  move_effect_journal_index_type const capture = top+move_effect_journal_index_offset_capture;
  move_effect_journal_index_type const movement = top+move_effect_journal_index_offset_movement;
  square const sq_departure = move_effect_journal[movement].u.piece_movement.from;
  PieNam const pi_departing = move_effect_journal[movement].u.piece_movement.moving;
  Flags const spec_pi_moving = move_effect_journal[movement].u.piece_movement.movingspec;
  SquareFlags const prom_square = BIT(WhPromSq)|BIT(BlPromSq);

  if (!TSTFLAGMASK(sq_spec[sq_departure],prom_square)
      && !is_pawn(pi_departing)
      && is_square_empty(sq_departure))
  {
    if (SentPionNeutral && is_piece_neutral(spec_pi_moving))
    {
      Flags const sentinelle_spec = all_pieces_flags|NeutralMask;
      move_effect_journal_do_piece_creation(move_effect_reason_sentinelles,
                                            sq_departure,
                                            sentinelle,
                                            sentinelle_spec);
    }
    else
    {
      Side sentinelle_side = SentPionAdverse ? advers(trait_ply) : trait_ply;

      if (flagparasent)
      {
        unsigned int prev_nr_other_sentinelles = number_of_pieces[advers(sentinelle_side)][sentinelle];
        PieNam const pi_captured = move_effect_journal[capture].u.piece_removal.removed;

        if (pi_captured==sentinelle)
          ++prev_nr_other_sentinelles;

        if (number_of_pieces[sentinelle_side][sentinelle]>prev_nr_other_sentinelles)
          sentinelle_side = no_side;
      }

      if (sentinelle_side!=no_side)
      {
        if (number_of_pieces[sentinelle_side][sentinelle]+1>sentinelles_max_nr_pawns[sentinelle_side]
            || number_of_pieces[White][sentinelle]+number_of_pieces[Black][sentinelle]+1 > sentinelles_max_nr_pawns_total)
          sentinelle_side = no_side;
      }

      if (sentinelle_side!=no_side)
      {
        Flags const sentinelle_spec = all_pieces_flags|BIT(sentinelle_side);
        move_effect_journal_do_piece_creation(move_effect_reason_sentinelles,
                                              sq_departure,
                                              sentinelle,
                                              sentinelle_spec);
      }
    }
  }
}

/* Try to solve in n half-moves.
 * @param si slice index
 * @param n maximum number of half moves
 * @return length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played is illegal
 *            this_move_is_illegal     the move being played is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 */
stip_length_type sentinelles_inserter_solve(slice_index si, stip_length_type n)
{
  stip_length_type result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParamListEnd();

  insert_sentinelle(slices[si].starter);
  result = solve(slices[si].next1,n);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Instrument a stipulation
 * @param si identifies root slice of stipulation
 */
void stip_insert_sentinelles_inserters(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_instrument_moves(si,STSentinellesInserter);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
