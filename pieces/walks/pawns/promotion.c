#include "pieces/walks/pawns/promotion.h"
#include "pieces/walks/pawns/promotee_sequence.h"
#include "solving/has_solution_type.h"
#include "stipulation/stipulation.h"
#include "stipulation/move.h"
#include "stipulation/pipe.h"
#include "solving/post_move_iteration.h"
#include "solving/pipe.h"
#include "debugging/trace.h"
#include "debugging/assert.h"

enum
{
  stack_size = max_nr_promotions_per_ply*maxply+1
};

static pieces_pawns_promotion_sequence_type promotion_stack[stack_size];
static unsigned int stack_pointer;

static post_move_iteration_id_type prev_post_move_iteration_id[stack_size];

move_effect_journal_index_type promotion_horizon;

/* Order in which the slice types for promotion execution appear
 */
static slice_type const promotion_slice_rank_order[] =
{
    STBeforePawnPromotion,
    STPawnToImitatorPromoter,
    STPawnPromoter,
    STChameleonChangePromoteeInto,
    STLandingAfterPawnPromotion
};

enum
{
  nr_promotion_slice_rank_order_elmts = sizeof promotion_slice_rank_order / sizeof promotion_slice_rank_order[0],
  nr_promotion_exit_slice_types = 1
};

static void insert_visit_promotion(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (!slice_insertion_insert_before(si,st))
  {
    stip_structure_traversal st_nested;
    branch_slice_insertion_state_type state_nested;
    slice_insertion_prepare_factored_order(si,
                                                     st,
                                                     &st_nested,&state_nested,
                                                     promotion_slice_rank_order,
                                                     nr_promotion_slice_rank_order_elmts,
                                                     nr_promotion_exit_slice_types);
    stip_traverse_structure_children_pipe(si,&st_nested);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Initialise a structure traversal for inserting slices
 * into the promotion execution sequence
 * @param st address of structure representing the traversal
 */
void promotion_init_slice_insertion_traversal(stip_structure_traversal *st)
{
  stip_structure_traversal_override_single(st,
                                           STBeforePawnPromotion,
                                           &insert_visit_promotion);
}

/* Insert slices into a promotion execution slices sequence.
 * The inserted slices are copies of the elements of prototypes; the elements of
 * prototypes are deallocated by promotion_insert_slices().
 * Each slice is inserted at a position that corresponds to its predefined rank.
 * @param si identifies starting point of insertion
 * @param context initial context of the insertion traversal; typically the
 *                current context of a surrounding traversal that has arrived
 *                at slice si
 * @param prototypes contains the prototypes whose copies are inserted
 * @param nr_prototypes number of elements of array prototypes
 */
void promotion_insert_slices(slice_index si,
                             stip_traversal_context_type context,
                             slice_index const prototypes[],
                             unsigned int nr_prototypes)
{
  stip_structure_traversal st;
  branch_slice_insertion_state_type state =
  {
      prototypes, nr_prototypes,
      promotion_slice_rank_order, nr_promotion_slice_rank_order_elmts, nr_promotion_exit_slice_types,
      branch_slice_rank_order_nonrecursive,
      0,
      si,
      0
  };

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",context);
  TraceFunctionParam("%u",nr_prototypes);
  TraceFunctionParamListEnd();

  slice_insertion_init_traversal(&st,&state,context);
  state.base_rank = get_slice_rank(slices[si].type,&state);
  stip_traverse_structure(si,&st);

  deallocate_slice_insertion_prototypes(prototypes,nr_prototypes);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_promoters(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  {
    slice_index const prototype = alloc_pipe(STPawnPromoter);
    promotion_insert_slices(si,st->context,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Instrumentall promotion slice sequences of the solving machinery with the
 * default promotion behavior
 * @param si identifies root slice of the solving machinery
 */
void promotion_instrument_solving_default(slice_index si)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,0);
  stip_structure_traversal_override_single(&st,
                                           STBeforePawnPromotion,
                                           &insert_promoters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

typedef struct
{
    slice_inserter_contextual_type const inserter;
} insertion_param_type;

static void insert_boundaries(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  {
    insertion_param_type const * const param = st->param;
    slice_index const prototypes[] = {
        alloc_pipe(STBeforePawnPromotion),
        alloc_pipe(STLandingAfterPawnPromotion)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    (*param->inserter)(si,st->context,prototypes,nr_prototypes);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Insert (the boundaries of) a promotion slice sequence into the solving
 * machinery
 * @param si identifies the root slice of the solving machinery
 * @param insertion_point type of insertion point slices
 * @param inserter slice insertion function for inserting from insertion_point
 *                 slices
 */
void promotion_insert_slice_sequence(slice_index si,
                                     slice_type insertion_point,
                                     slice_inserter_contextual_type inserter)
{
  insertion_param_type param = { inserter };
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,&param);
  stip_structure_traversal_override_single(&st,
                                           insertion_point,
                                           &insert_boundaries);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Find the last square occupied by a piece since we last checked.
 * @param base index of move effects that have already been dealt with
 * @return the square; initsquare if there isn't any
 */
square find_potential_promotion_square(move_effect_journal_index_type base)
{
  move_effect_journal_index_type curr = move_effect_journal_base[nbply+1];

  while (curr>base)
  {
    --curr;

    switch (move_effect_journal[curr].type)
    {
      case move_effect_piece_movement:
        return move_effect_journal[curr].u.piece_movement.to;

      case move_effect_piece_readdition:
        return move_effect_journal[curr].u.piece_addition.on;

      default:
        break;
    }
  }

  return initsquare;
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
void pawn_promoter_solve(slice_index si)
{
  move_effect_journal_index_type const save_horizon = promotion_horizon;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  {
    square const sq_potential_promotion = find_potential_promotion_square(promotion_horizon);

    assert(stack_pointer<stack_size);

    promotion_horizon = move_effect_journal_base[nbply+1];

    if (post_move_iteration_id[nbply]!=prev_post_move_iteration_id[stack_pointer])
      pieces_pawns_start_promotee_sequence(sq_potential_promotion,
                                           &promotion_stack[stack_pointer]);

    if (promotion_stack[stack_pointer].promotee==Empty)
    {
      ++stack_pointer;
      pipe_solve_delegate(si);
      --stack_pointer;
    }
    else
    {
      move_effect_journal_do_walk_change(move_effect_reason_pawn_promotion,
                                         sq_potential_promotion,
                                         promotion_stack[stack_pointer].promotee);

      ++stack_pointer;
      pipe_solve_delegate(si);
      --stack_pointer;

      if (!post_move_iteration_locked[nbply])
      {
        pieces_pawns_continue_promotee_sequence(&promotion_stack[stack_pointer]);
        if (promotion_stack[stack_pointer].promotee!=Empty)
          lock_post_move_iterations();
      }

      prev_post_move_iteration_id[stack_pointer] = post_move_iteration_id[nbply];
    }

    promotion_horizon = save_horizon;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
