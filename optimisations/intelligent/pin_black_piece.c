#include "optimisations/intelligent/pin_black_piece.h"
#include "pydata.h"
#include "optimisations/intelligent/intelligent.h"
#include "optimisations/intelligent/count_nr_of_moves.h"
#include "debugging/trace.h"

#include <assert.h>
#include <stdlib.h>

/* Pin the piece on a specific square with an original rider
 * @param sq_to_be_pinned position of piece to be pinned
 * @param pin_on where to put pinner
 * @param pinner_index identifiespinnter
 * @param is_pin_on_diagonal is the piece to be pinned on a diagonal
 */
static void pin_by_rider(unsigned int pinner_index,
                         piece pinner_type,
                         square pin_from,
                         void (*go_on)(void))
{
  square const pinner_comes_from = white[pinner_index].diagram_square;

  TraceFunctionEntry(__func__);
  TracePiece(pinner_type);
  TraceSquare(pinner_comes_from);
  TraceSquare(pin_from);
  TraceFunctionParamListEnd();

  if (intelligent_reserve_officer_moves_from_to(pinner_comes_from,
                                                pinner_type,
                                                pin_from))
  {
    SetPiece(pinner_type,pin_from,white[pinner_index].flags);
    (*go_on)();
    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Pin the piece on a specific square with a promoted rider
 * @param sq_to_be_pinned position of piece to be pinned
 * @param pin_on where to put pinner
 * @param pinner_index identifiespinnter
 * @param is_pin_on_diagonal is the piece to be pinned on a diagonal
 */
static void pin_by_promoted_pawn(unsigned int pinner_index,
                                 square pin_from,
                                 boolean is_pin_on_diagonal,
                                 void (*go_on)(void))
{
  piece const minor_pinner_type = is_pin_on_diagonal ? fb : tb;
  square const pinner_comes_from = white[pinner_index].diagram_square;

  TraceFunctionEntry(__func__);
  TraceSquare(pinner_comes_from);
  TraceSquare(pin_from);
  TraceFunctionParam("%u",is_pin_on_diagonal);
  TraceFunctionParamListEnd();

  if (intelligent_reserve_promoting_white_pawn_moves_from_to(pinner_comes_from,
                                                             db,
                                                             pin_from))
  {
    SetPiece(db,pin_from,white[pinner_index].flags);
    (*go_on)();
    intelligent_unreserve();
  }

  if (intelligent_reserve_promoting_white_pawn_moves_from_to(pinner_comes_from,
                                                             minor_pinner_type,
                                                             pin_from))
  {
    SetPiece(minor_pinner_type,pin_from,white[pinner_index].flags);
    (*go_on)();
    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Pin the piece on a specific square with a specific piece
 * @param pinner_index identifiespinnter
 * @param pin_from where to put pinner
 * @param is_pin_on_diagonal is the piece to be pinned on a diagonal
 */
static void pin_using_specific_piece_on(unsigned int pinner_index,
                                        square pin_from,
                                        boolean is_pin_on_diagonal,
                                        void (*go_on)(void))
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",pinner_index);
  TraceSquare(pin_from);
  TraceFunctionParam("%u",is_pin_on_diagonal);
  TraceFunctionParamListEnd();

  switch (white[pinner_index].type)
  {
    case db:
      pin_by_rider(pinner_index,db,pin_from,go_on);
      break;

    case tb:
      if (!is_pin_on_diagonal)
        pin_by_rider(pinner_index,tb,pin_from,go_on);
      break;

    case fb:
      if (is_pin_on_diagonal)
        pin_by_rider(pinner_index,fb,pin_from,go_on);
      break;

    case cb:
      break;

    case pb:
      pin_by_promoted_pawn(pinner_index,pin_from,is_pin_on_diagonal,go_on);
      break;

    default:
      assert(0);
      break;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Find out whether a black piece can be pinned
 * @param piece_pos position of piece to be pinned
 * @return direction of pin line from black king square to piece_pos
 *         0         otherwise
 */
int intelligent_is_black_piece_pinnable(square piece_pos)
{
  int const diff = piece_pos-king_square[Black];
  int result = CheckDir[Queen][diff];

  TraceFunctionEntry(__func__);
  TraceSquare(piece_pos);
  TraceFunctionParamListEnd();

  if (result!=0 && !is_line_empty(king_square[Black],piece_pos,result))
    result = 0;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%d",result);
  TraceFunctionResultEnd();
  return result;
}


/* Pin a pinnable black piece
 * @param piece_pos position of piece to be pinned
 * @param pin_dir direction of pin line from black king square via piece_pos
 * @param go_on how to go on
 * @pre pin_dir!=0
 * @pre the piece at piece_pos is pinnable along pin_dir
 */
void intelligent_pin_pinnable_black_piece(square piece_pos,
                                          int pin_dir,
                                          void (*go_on)(void))
{
  TraceFunctionEntry(__func__);
  TraceSquare(piece_pos);
  TraceFunctionParamListEnd();

  assert(pin_dir!=0);

  if (intelligent_reserve_pinner())
  {
    boolean const is_pin_on_diagonal = SquareCol(piece_pos+pin_dir)==SquareCol(piece_pos);

    square pin_on;

    remember_to_keep_rider_line_open(king_square[Black],piece_pos,pin_dir,+1);

    for (pin_on = piece_pos+pin_dir; e[pin_on]==vide; pin_on += pin_dir)
    {
      if (nr_reasons_for_staying_empty[pin_on]==0)
      {
        unsigned int pinner_index;
        for (pinner_index = 1; pinner_index<MaxPiece[White]; ++pinner_index)
        {
          if (white[pinner_index].usage==piece_is_unused)
          {
            white[pinner_index].usage = piece_pins;
            pin_using_specific_piece_on(pinner_index,pin_on,is_pin_on_diagonal,go_on);
            white[pinner_index].usage = piece_is_unused;
          }
        }

        e[pin_on] = vide;
        spec[pin_on] = EmptySpec;
      }

      ++nr_reasons_for_staying_empty[pin_on];
    }

    for (pin_on -= pin_dir; pin_on!=piece_pos; pin_on -= pin_dir)
      --nr_reasons_for_staying_empty[pin_on];

    remember_to_keep_rider_line_open(king_square[Black],piece_pos,pin_dir,-1);

    intelligent_unreserve();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Pin a black piece
 * @param piece_pos position of piece to be pinned
 * @param go_on how to go on
 */
void intelligent_pin_black_piece(square piece_pos, void (*go_on)(void))
{
  int const pin_dir = intelligent_is_black_piece_pinnable(piece_pos);

  TraceFunctionEntry(__func__);
  TraceSquare(piece_pos);
  TraceFunctionParamListEnd();

  if (pin_dir!=0) /* we can only pin on queen lines */
    intelligent_pin_pinnable_black_piece(piece_pos,pin_dir,go_on);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
