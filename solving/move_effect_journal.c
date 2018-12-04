#include "solving/move_effect_journal.h"
#include "pieces/pieces.h"
#include "position/position.h"
#include "solving/pipe.h"
#include "solving/machinery/twin.h"
#include "stipulation/stipulation.h"
#include "stipulation/branch.h"
#include "stipulation/pipe.h"
#include "stipulation/modifier.h"
#include "debugging/trace.h"
#include "debugging/assert.h"

move_effect_journal_entry_type move_effect_journal[move_effect_journal_size];

/* starting at 1 simplifies pointer arithmetic in undo_move_effects */
move_effect_journal_index_type move_effect_journal_base[maxply+1] = { 1, 1 };

move_effect_journal_index_type move_effect_journal_index_offset_capture = 0;
move_effect_journal_index_type move_effect_journal_index_offset_movement = 1;
move_effect_journal_index_type move_effect_journal_index_offset_other_effects = 2;

move_effect_journal_index_type king_square_horizon;

/* Reserve space for an effect in each move before the capture (e.g. for
 * Singlebox Type 3 promotions). Conditions that do this have to make sure
 * that every move has such an effect, possibly by adding a null effect to
 * fill the reserved gap.
 */
void move_effect_journal_register_pre_capture_effect(void)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  ++move_effect_journal_index_offset_capture;
  ++move_effect_journal_index_offset_movement;
  ++move_effect_journal_index_offset_other_effects;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Reset the move effects journal from pre-capture effect reservations
 */
void move_effect_journal_reset(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  move_effect_journal_index_offset_capture = 0;
  move_effect_journal_index_offset_movement = 1;
  move_effect_journal_index_offset_other_effects = 2;

  pipe_solve_delegate(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

#if defined(DOTRACE)
unsigned long move_effect_journal_next_id;
#endif

/* Allocate an entry
 * @param type type of the effect
 * @param reason reason of the effect
 * @return address of allocated entry
 * @note terminates the program if the entries are exhausted
 */
move_effect_journal_entry_type *move_effect_journal_allocate_entry(move_effect_type type,
                                                                   move_effect_reason_type reason)
{
  move_effect_journal_index_type const top = move_effect_journal_base[nbply+1];
  move_effect_journal_entry_type * const result = &move_effect_journal[top];

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",type);
  TraceFunctionParam("%u",reason);
  TraceFunctionParamListEnd();

  assert(move_effect_journal_base[nbply+1]+1<move_effect_journal_size);

  result->type = type;
  result->reason = reason;

#if defined(DOTRACE)
  result->id = move_effect_journal_next_id++;
  TraceValue("%lu",result->id);
  TraceEOL();
#endif

  ++move_effect_journal_base[nbply+1];
  TraceValue("%u",move_effect_journal_base[nbply+1]);
  TraceEOL();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
  return result;
}

#include "conditions/actuated_revolving_centre.h"
#include "position/effects/piece_removal.h"
#include "position/effects/piece_creation.h"
#include "position/effects/piece_movement.h"
#include "position/effects/piece_exchange.h"
#include "position/effects/board_transformation.h"

/* Follow the captured or a moved piece through the "other" effects of a move
 * @param ply ply in which the move was played
 * @param followed_id id of the piece to be followed
 * @param pos position of the piece after the inital capture removal and piece movement have taken place
 * @return the position of the piece with the "other" effect applied
 *         initsquare if the piece is not on the board after the "other" effects
 */
square move_effect_journal_follow_piece_through_other_effects(ply ply,
                                                              PieceIdType followed_id,
                                                              square pos)
{
  move_effect_journal_index_type const base = move_effect_journal_base[ply];
  move_effect_journal_index_type const top = move_effect_journal_base[ply+1];
  move_effect_journal_index_type other;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",ply);
  TraceFunctionParam("%x",followed_id);
  TraceSquare(pos);
  TraceFunctionParamListEnd();

  for (other = base+move_effect_journal_index_offset_other_effects;
       other<top;
       ++other)
  {
    TraceValue("%u",move_effect_journal[other].type);
    TraceEOL();
    switch (move_effect_journal[other].type)
    {
      case move_effect_piece_removal:
        pos = position_piece_removal_follow_piece(followed_id,other,pos);
        break;

      case move_effect_piece_readdition:
      case move_effect_piece_creation:
        pos = position_piece_creation_follow_piece(followed_id,other,pos);
        break;

      case move_effect_piece_movement:
        pos = position_piece_movement_follow_piece(followed_id,other,pos);
        break;

      case move_effect_piece_exchange:
        pos = position_piece_exchange_follow_piece(followed_id,other,pos);
        break;

      case move_effect_board_transformation:
        pos = position_board_transformation_follow_piece(followed_id,other,pos);
        break;

      case move_effect_centre_revolution:
        pos = actuated_revolving_centre_revolve_square(pos);
        break;

      case move_effect_none:
      case move_effect_no_piece_removal:
      case move_effect_walk_change:
      case move_effect_side_change:
      case move_effect_king_square_movement:
      case move_effect_flags_change:
      case move_effect_imitator_addition:
      case move_effect_imitator_movement:
      case move_effect_remember_ghost:
      case move_effect_forget_ghost:
      case move_effect_half_neutral_deneutralisation:
      case move_effect_half_neutral_neutralisation:
      case move_effect_square_block:
      case move_effect_bgl_adjustment:
      case move_effect_strict_sat_adjustment:
      case move_effect_disable_castling_right:
      case move_effect_enable_castling_right:
      case move_effect_remember_ep_capture_potential:
      case move_effect_remember_duellist:
      case move_effect_remember_parachuted:
      case move_effect_remember_volcanic:
      case move_effect_swap_volcanic:
        /* nothing */
        break;

      default:
        assert(0);
        break;
    }
  }

  TraceFunctionExit(__func__);
  TraceSquare(pos);
  TraceFunctionResultEnd();
  return pos;
}

static struct
{
    move_effect_doer undoer;
    move_effect_doer redoer;
} move_effect_doers[nr_move_effect_types];

static void move_effect_none_do(move_effect_journal_entry_type const *entry)
{
}

void move_effect_journal_init_move_effect_doers(void)
{
  move_effect_type t;
  for (t = 0; t!=nr_move_effect_types; ++t)
  {
    move_effect_doers[t].undoer = &move_effect_none_do;
    move_effect_doers[t].redoer = &move_effect_none_do;
  }
}

void move_effect_journal_set_effect_doers(move_effect_type type,
                                          move_effect_doer undoer,
                                          move_effect_doer redoer)
{
  move_effect_doers[type].undoer = undoer;
  move_effect_doers[type].redoer = redoer;
}

/* Redo the effects of the current move in ply nbply
 */
void redo_move_effects(void)
{
  move_effect_journal_index_type const parent_top = move_effect_journal_base[nbply];
  move_effect_journal_index_type const top = move_effect_journal_base[nbply+1];
  move_effect_journal_entry_type const *top_entry = &move_effect_journal[top];
  move_effect_journal_entry_type const *entry;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  assert(parent_top<=top);

  for (entry = &move_effect_journal[parent_top]; entry!=top_entry; ++entry)
  {
#if defined(DOTRACE)
    TraceValue("%u",entry->type);
    TraceEOL();
    TraceValue("%lu",entry->id);
    TraceEOL();
#endif

    assert(move_effect_doers[entry->type].redoer!=0);
    (*move_effect_doers[entry->type].redoer)(entry);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Undo the effects of the current move in ply nbply
 */
void undo_move_effects(void)
{
  move_effect_journal_index_type const parent_top = move_effect_journal_base[nbply];
  move_effect_journal_entry_type const *parent_top_entry = &move_effect_journal[parent_top-1];
  move_effect_journal_index_type const top = move_effect_journal_base[nbply+1];
  move_effect_journal_entry_type const *entry;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  assert(parent_top>0);
  assert(top>=parent_top);

  for (entry = &move_effect_journal[top-1]; entry!=parent_top_entry; --entry)
  {
#if defined(DOTRACE)
    TraceValue("%u",entry->type);
    TraceEOL();
    TraceValue("%lu",entry->id);
    TraceEOL();
#endif


    assert(move_effect_doers[entry->type].undoer!=0);
    (*move_effect_doers[entry->type].undoer)(entry);
  }

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
void move_effect_journal_undoer_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  move_effect_journal_base[nbply+1] = move_effect_journal_base[nbply];
  pipe_solve_delegate(si);

  undo_move_effects();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
