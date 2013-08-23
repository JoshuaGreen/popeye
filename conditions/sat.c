#include "conditions/sat.h"
#include "pydata.h"
#include "stipulation/has_solution_type.h"
#include "stipulation/stipulation.h"
#include "stipulation/pipe.h"
#include "stipulation/branch.h"
#include "stipulation/move.h"
#include "stipulation/structure_traversal.h"
#include "stipulation/temporary_hacks.h"
#include "solving/legal_move_counter.h"
#include "solving/check.h"
#include "debugging/trace.h"

#include <assert.h>

boolean StrictSAT[nr_sides];
unsigned int SAT_max_nr_allowed_flights[nr_sides];

static slice_index strict_sat_flight_tester;

static boolean find_flights(slice_index si,
                            Side side_in_check,
                            unsigned int nr_flights_to_find)
{
  unsigned int nr_flights_found = 0;
  vec_index_type i;
  PieNam const king_type = e[king_square[side_in_check]];
  Flags const king_flags = spec[king_square[side_in_check]];

  empty_square(king_square[side_in_check]);

  for (i = vec_queen_start; i<=vec_queen_end; ++i)
  {
    king_square[side_in_check] += vec[i];
    if ((is_square_empty(king_square[side_in_check])
         || TSTFLAG(spec[king_square[side_in_check]],advers(side_in_check)))
        && king_square[side_in_check]!=king_square[advers(side_in_check)]
        && !is_in_check(slices[si].next1,side_in_check))
      ++nr_flights_found;
    king_square[side_in_check] -= vec[i];
  }

  occupy_square(king_square[side_in_check],king_type,king_flags);

  return nr_flights_found>nr_flights_to_find;
}

/* Determine whether a side is in check
 * @param si identifies the check tester
 * @param side_in_check which side?
 * @return true iff side_in_check is in check according to slice si
 */
boolean sat_check_tester_is_in_check(slice_index si, Side side_in_check)
{
  boolean result;

  if (SAT_max_nr_allowed_flights[side_in_check]==0)
    result = true;
  else
    result = find_flights(si,side_in_check,SAT_max_nr_allowed_flights[side_in_check]-1);

  return result;
}

/* Determine whether a side is in check
 * @param si identifies the check tester
 * @param side_in_check which side?
 * @return true iff side_in_check is in check according to slice si
 */
boolean strictsat_check_tester_is_in_check(slice_index si, Side side_in_check)
{
  boolean result;
  unsigned int max_nr_allowed_flights = SAT_max_nr_allowed_flights[side_in_check];

  if (StrictSAT[side_in_check])
  {
    if (!is_in_check(slices[si].next1,side_in_check))
      --max_nr_allowed_flights;
  }

  if (max_nr_allowed_flights==0)
    result = true;
  else
    result = find_flights(si,side_in_check,max_nr_allowed_flights-1);

  return result;
}

/* Determine whether a side is in check
 * @param si identifies the check tester
 * @param side_in_check which side?
 * @return true iff side_in_check is in check according to slice si
 */
boolean satxy_check_tester_is_in_check(slice_index si, Side side_in_check)
{
  boolean result;
  unsigned int max_nr_allowed_flights = SAT_max_nr_allowed_flights[side_in_check];

  if (!is_in_check(slices[si].next1,side_in_check))
    --max_nr_allowed_flights;

  if (max_nr_allowed_flights==0)
    result = true;
  else
    result = find_flights(si,side_in_check,max_nr_allowed_flights-1);

  return result;
}

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
stip_length_type strict_sat_initialiser_solve(slice_index si,
                                              stip_length_type n)
{
  stip_length_type result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParamListEnd();

  strict_sat_flight_tester = branch_find_slice(STStrictSATCheckTester,
                                               slices[temporary_hack_check_tester].next2,
                                               stip_traversal_context_intro);
  assert(strict_sat_flight_tester!=no_slice);
  StrictSAT[White] = is_in_check(slices[strict_sat_flight_tester].next1,White);
  StrictSAT[Black] = is_in_check(slices[strict_sat_flight_tester].next1,Black);

  result = solve(slices[si].next1,n);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Adjust the Strict SAT state
 * @param diff adjustment
 */
static void do_strict_sat_adjustment(Side side)
{
  move_effect_journal_index_type const top = move_effect_journal_base[nbply+1];
  move_effect_journal_entry_type * const top_elmt = &move_effect_journal[top];

  TraceFunctionEntry(__func__);
  TraceEnumerator(Side,side,"");
  TraceFunctionParamListEnd();

  assert(move_effect_journal_base[nbply+1]+1<move_effect_journal_size);

  top_elmt->type = move_effect_strict_sat_adjustment;
  top_elmt->reason = move_effect_reason_sat_adjustment;
  top_elmt->u.strict_sat_adjustment.side = side;
 #if defined(DOTRACE)
  top_elmt->id = move_effect_journal_next_id++;
  TraceValue("%lu\n",top_elmt->id);
 #endif

  ++move_effect_journal_base[nbply+1];

  StrictSAT[side] = true;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Undo a Strict SAT state adjustment
 * @param curr identifies the adjustment effect
 */
void move_effect_journal_undo_strict_sat_adjustment(move_effect_journal_index_type curr)
{
  Side const side = move_effect_journal[curr].u.strict_sat_adjustment.side;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",curr);
  TraceFunctionParamListEnd();

#if defined(DOTRACE)
  TraceValue("%lu\n",move_effect_journal[curr].id);
#endif

  StrictSAT[side] = false;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Redo a Strict SAT state adjustment
 * @param curr identifies the adjustment effect
 */
void move_effect_journal_redo_strict_sat_adjustment(move_effect_journal_index_type curr)
{
  Side const side = move_effect_journal[curr].u.strict_sat_adjustment.side;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",curr);
  TraceFunctionParamListEnd();

#if defined(DOTRACE)
  TraceValue("%lu\n",move_effect_journal[curr].id);
#endif

  StrictSAT[side] = true;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

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
stip_length_type strict_sat_updater_solve(slice_index si, stip_length_type n)
{
  stip_length_type result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParamListEnd();

  if (!StrictSAT[White] && is_in_check(slices[strict_sat_flight_tester].next1,White))
    do_strict_sat_adjustment(White);
  if (!StrictSAT[Black] && is_in_check(slices[strict_sat_flight_tester].next1,Black))
    do_strict_sat_adjustment(Black);

  result = solve(slices[si].next1,n);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

static void instrument_move_with_updater(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  {
    slice_index const prototype = alloc_pipe(STStrictSATUpdater);
    branch_insert_slices_contextual(si,st->context,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Instrument a stipulation
 * @param si identifies root slice of stipulation
 */
void strictsat_initialise_solving(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  {
    stip_structure_traversal st;
    stip_structure_traversal_init(&st,0);
    stip_structure_traversal_override_single(&st,STMove,&instrument_move_with_updater);
    stip_traverse_structure(si,&st);
  }

  solving_instrument_check_testing(si,STStrictSATCheckTester);

  {
    slice_index const prototype = alloc_pipe(STStrictSATInitialiser);
    branch_insert_slices(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void sat_initialise_solving(slice_index si)
{
  if (SAT_max_nr_allowed_flights[White]>1 || SAT_max_nr_allowed_flights[Black]>1)
    solving_instrument_check_testing(si,STSATxyCheckTester);
  else
    solving_instrument_check_testing(si,STSATCheckTester);
}
