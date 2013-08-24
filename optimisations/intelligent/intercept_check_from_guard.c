#include "optimisations/intelligent/intercept_check_from_guard.h"
#include "pieces/pieces.h"
#include "optimisations/intelligent/intelligent.h"
#include "optimisations/intelligent/guard_flights.h"
#include "optimisations/intelligent/count_nr_of_moves.h"
#include "optimisations/intelligent/guard_flights.h"
#include "optimisations/intelligent/place_black_piece.h"
#include "solving/moving_pawn_promotion.h"
#include "debugging/trace.h"

#include <assert.h>

/* Place a white officer to intercept a check to the black king
 * @param officer_type type of officer
 * @param to_be_intercepted where to intercept
 * @param index_of_intercepting_piece identifies the pawn
 */
static void place_officer(PieNam officer_type,
                          square to_be_intercepted,
                          unsigned int index_of_intercepting_piece)
{
  Flags const intercepter_flags = white[index_of_intercepting_piece].flags;

  TraceFunctionEntry(__func__);
  TracePiece(officer_type);
  TraceSquare(to_be_intercepted);
  TraceValue("%u",index_of_intercepting_piece);
  TraceFunctionParamListEnd();

  if (/* avoid duplicate: if intercepter has already been used as guarding
       * piece, it shouldn't guard now again */
      !(index_of_intercepting_piece<index_of_guarding_piece
        && GuardDir[officer_type-Pawn][to_be_intercepted].dir!=0))
  {
    occupy_square(to_be_intercepted,officer_type,intercepter_flags);
    intelligent_continue_guarding_flights();
    empty_square(to_be_intercepted);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Place a white promotee to intercept a check to the black king
 * @param promotee_type type of promotee
 * @param to_be_intercepted where to intercept
 * @param index_of_intercepting_piece identifies the pawn
 */
static void place_promotee(PieNam promotee_type,
                           square to_be_intercepted,
                           unsigned int index_of_intercepting_piece)
{
  square const intercepter_diagram_square = white[index_of_intercepting_piece].diagram_square;

  TraceFunctionEntry(__func__);
  TracePiece(promotee_type);
  TraceSquare(to_be_intercepted);
  TraceValue("%u",index_of_intercepting_piece);
  TraceFunctionParamListEnd();

  if (intelligent_reserve_promoting_white_pawn_moves_from_to(intercepter_diagram_square,
                                                             promotee_type,
                                                             to_be_intercepted))
  {
    place_officer(promotee_type,to_be_intercepted,index_of_intercepting_piece);
    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Intercept a check by a white rider white an promoted pawn
 * @param to_be_intercepted where to intercept
 * @param index_of_intercepting_piece identifies the pawn
 * @param is_diagonal true iff the check is on a diagonal
 */
static void promoted_pawn(square to_be_intercepted,
                          unsigned int index_of_intercepting_piece,
                          boolean is_diagonal)
{
  TraceFunctionEntry(__func__);
  TraceSquare(to_be_intercepted);
  TraceValue("%u",index_of_intercepting_piece);
  TraceValue("%u",is_diagonal);
  TraceFunctionParamListEnd();

  if (intelligent_can_promoted_white_pawn_theoretically_move_to(index_of_intercepting_piece,
                                                                to_be_intercepted))
  {
    PieNam pp;
    for (pp = pieces_pawns_promotee_chain[pieces_pawns_promotee_chain_orthodox][Empty]; pp!=Empty; pp = pieces_pawns_promotee_chain[pieces_pawns_promotee_chain_orthodox][pp])
      switch (pp)
      {
        case Queen:
          break;

        case Rook:
          if (is_diagonal)
            place_promotee(Rook,to_be_intercepted,index_of_intercepting_piece);
          break;

        case Bishop:
          if (!is_diagonal)
            place_promotee(Bishop,to_be_intercepted,index_of_intercepting_piece);
          break;

        case Knight:
          place_promotee(Knight,to_be_intercepted,index_of_intercepting_piece);
          break;

        default:
          assert(0);
          break;
      }
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Intercept a check by a white rider white an unpromoted pawn
 * @param to_be_intercepted where to intercept
 * @param index_of_intercepting_piece identifies the pawn
 */
static void unpromoted_pawn(square to_be_intercepted,
                            unsigned int index_of_intercepting_piece)
{
  square const intercepter_diagram_square = white[index_of_intercepting_piece].diagram_square;
  Flags const intercepter_flags = white[index_of_intercepting_piece].flags;
  numvec const guard_dir = GuardDir[Pawn-Pawn][to_be_intercepted].dir;

  TraceFunctionEntry(__func__);
  TraceSquare(to_be_intercepted);
  TraceValue("%u",index_of_intercepting_piece);
  TraceFunctionParamListEnd();

  if (guard_dir!=guard_dir_check_uninterceptable
      /* avoid duplicate: if intercepter has already been used as guarding
       * piece, it shouldn't guard now again */
      && !(index_of_intercepting_piece<index_of_guarding_piece
           && guard_dir==guard_dir_guard_uninterceptable)
      && intelligent_reserve_white_pawn_moves_from_to_no_promotion(intercepter_diagram_square,
                                                                   to_be_intercepted))
  {
    occupy_square(to_be_intercepted,Pawn,intercepter_flags);
    intelligent_continue_guarding_flights();
    empty_square(to_be_intercepted);
    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Intercept a check by a white rider white a white officer
 * @param to_be_intercepted where to intercept
 * @param index_of_intercepting_piece identifies the intercepting officer
 */
static void officer(square to_be_intercepted,
                    unsigned int index_of_intercepting_piece)
{
  square const officer_diagram_square = white[index_of_intercepting_piece].diagram_square;
  PieNam const officer_type = white[index_of_intercepting_piece].type;

  TraceFunctionEntry(__func__);
  TraceSquare(to_be_intercepted);
  TraceValue("%u",index_of_intercepting_piece);
  TraceFunctionParamListEnd();

  if (intelligent_reserve_officer_moves_from_to(White,
                                                officer_diagram_square,
                                                officer_type,
                                                to_be_intercepted))
  {
    place_officer(officer_type,to_be_intercepted,index_of_intercepting_piece);
    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Intercept a check by a white rider on the flight guarded by the rider
 * @param to_be_intercepted where to intercept
 */
void intercept_check_on_guarded_square(square to_be_intercepted)
{
  unsigned int intercepter_index;
  boolean const is_diagonal = SquareCol(to_be_intercepted)==SquareCol(king_square[Black]);

  TraceFunctionEntry(__func__);
  TraceSquare(to_be_intercepted);
  TraceFunctionParamListEnd();

  if (intelligent_reserve_masses(White,1))
  {
    for (intercepter_index = 1;
         intercepter_index<MaxPiece[White];
         ++intercepter_index)
    {
      TraceValue("%u",intercepter_index);
      TraceEnumerator(piece_usage,white[intercepter_index].usage,"\n");
      if (white[intercepter_index].usage==piece_is_unused)
      {
        PieNam const intercepter_type = white[intercepter_index].type;
        white[intercepter_index].usage = piece_intercepts_check_from_guard;

        switch (intercepter_type)
        {
          case Queen:
            break;

          case Rook:
            if (is_diagonal)
              officer(to_be_intercepted,intercepter_index);
              break;

          case Bishop:
            if (!is_diagonal)
              officer(to_be_intercepted,intercepter_index);
            break;

          case Knight:
            officer(to_be_intercepted,intercepter_index);
            break;

          case Pawn:
            if (!TSTFLAGMASK(sq_spec[to_be_intercepted],BIT(WhBaseSq)|BIT(WhPromSq)))
              unpromoted_pawn(to_be_intercepted,intercepter_index);
            promoted_pawn(to_be_intercepted,intercepter_index,is_diagonal);
            break;

          default:
            assert(0);
            break;
        }

        white[intercepter_index].usage = piece_is_unused;
      }
    }

    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Intercept an orthogonal check with a pinned promoted black piece
 * @param placed_on where to place the pinned black piece
 */
static void place_promoted_black_pawn(square placed_on,
                                      unsigned int placed_index)
{
  TraceFunctionEntry(__func__);
  TraceSquare(placed_on);
  TraceFunctionParam("%u",placed_index);
  TraceFunctionParamListEnd();

  if (intelligent_can_promoted_black_pawn_theoretically_move_to(placed_index,
                                                                placed_on))
  {
    PieNam pp;
    for (pp = pieces_pawns_promotee_chain[pieces_pawns_promotee_chain_orthodox][Empty]; pp!=Empty; pp = pieces_pawns_promotee_chain[pieces_pawns_promotee_chain_orthodox][pp])
      switch (pp)
      {
        case Queen:
        case Rook:
        case Bishop:
          intelligent_place_pinned_promoted_black_rider(placed_index,
                                                        Bishop,
                                                        placed_on,
                                                        &intelligent_continue_guarding_flights);
          break;

        case Knight:
          intelligent_place_pinned_promoted_black_knight(placed_index,
                                                         placed_on,
                                                         &intelligent_continue_guarding_flights);
          break;

        default:
          assert(0);
          break;
      }
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Intercept an orthogonal check with a pinned black piece
 * @param placed_on where to place the pinned black piece
 */
void intelligent_intercept_orthogonal_check_by_pin(square placed_on)
{
  TraceFunctionEntry(__func__);
  TraceSquare(placed_on);
  TraceFunctionParamListEnd();

  if (intelligent_reserve_masses(Black,1))
  {
    unsigned int placed_index;
    for (placed_index = 1; placed_index<MaxPiece[Black]; ++placed_index)
      if (black[placed_index].usage==piece_is_unused)
      {
        black[placed_index].usage = piece_intercepts_check_from_guard;

        switch (black[placed_index].type)
        {
          case Queen:
          case Rook:
          case Bishop:
            intelligent_place_pinned_black_rider(placed_index,
                                                 placed_on,
                                                 &intelligent_continue_guarding_flights);
            break;

          case Knight:
            intelligent_place_pinned_black_knight(placed_index,
                                                  placed_on,
                                                  &intelligent_continue_guarding_flights);
            break;

          case Pawn:
            intelligent_place_pinned_unpromoted_black_pawn(placed_index,
                                                           placed_on,
                                                           &intelligent_continue_guarding_flights);
            place_promoted_black_pawn(placed_on,placed_index);
            break;

          default:
            assert(0);
            break;
        }

        black[placed_index].usage = piece_is_unused;
      }

    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
