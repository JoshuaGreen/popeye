/******************** MODIFICATIONS to pyint.c **************************
 **
 ** Date       Who  What
 **
 ** 2006/06/14 TLi  bug fix in function guards_black_flight()
 **
 ** 2007/12/27 TLi  bug fix in function stalemate_immobilise_black()
 **
 **************************** End of List ******************************/

#include "optimisations/intelligent/intelligent.h"

#include "pieces/walks/pawns/en_passant.h"
#include "solving/proofgames.h"
#include "solving/machinery/solve.h"
#include "solving/castling.h"
#include "solving/check.h"
#include "solving/temporary_hacks.h"
#include "solving/pipe.h"
#include "stipulation/help_play/branch.h"
#include "stipulation/fork.h"
#include "stipulation/pipe.h"
#include "stipulation/branch.h"
#include "stipulation/slice_insertion.h"
#include "optimisations/intelligent/count_nr_of_moves.h"
#include "optimisations/intelligent/guard_flights.h"
#include "optimisations/intelligent/moves_left.h"
#include "optimisations/intelligent/stalemate/finish.h"
#include "optimisations/intelligent/proof.h"
#include "optimisations/intelligent/duplicate_avoider.h"
#include "optimisations/intelligent/place_black_piece.h"
#include "optimisations/intelligent/mate/finish.h"
#include "optimisations/intelligent/mate/generate_checking_moves.h"
#include "optimisations/intelligent/mate/generate_doublechecking_moves.h"
#include "optimisations/intelligent/piece_usage.h"
#include "optimisations/intelligent/proof.h"
#include "options/maxsolutions/guard.h"
#include "options/maxtime.h"
#include "output/plaintext/plaintext.h"
#include "output/plaintext/pieces.h"
#include "debugging/trace.h"
#include "pieces/pieces.h"
#include "platform/maxtime.h"
#include "options/options.h"

#include "debugging/assert.h"
#include <stdio.h>
#include <stdlib.h>

typedef unsigned int index_type;

goal_type goal_to_be_reached;

unsigned int MaxPiece[nr_sides];

PIECE white[nr_squares_on_board];
PIECE black[nr_squares_on_board];
unsigned int moves_to_white_prom[nr_squares_on_board];

PIECE target_position[MaxPieceId+1];

boolean solutions_found;

boolean testcastling;

unsigned int MovesRequired[nr_sides][maxply+1];
unsigned int CapturesLeft[maxply+1];

unsigned int PieceId2index[MaxPieceId+1];

unsigned int nr_reasons_for_staying_empty[maxsquare+4];

typedef struct
{
  Flags       spec[nr_squares_on_board];
  piece_walk_type      e[nr_squares_on_board];
  square      rn_sic, rb_sic;
} stored_position_type;

static stored_position_type initial_position;

static void StorePosition(stored_position_type *store)
{
  store->rn_sic = being_solved.king_square[Black];
  store->rb_sic = being_solved.king_square[White];

  {
    unsigned int i;
    for (i = 0; i<nr_squares_on_board; i++)
    {
      store->e[i] = get_walk_of_piece_on_square(boardnum[i]);
      store->spec[i] = being_solved.spec[boardnum[i]];
    }
  }
}

static void ResetPosition(stored_position_type const *store)
{
  {
    piece_walk_type p;
    for (p = King; p<nr_piece_walks; ++p)
    {
      being_solved.number_of_pieces[White][p] = 0;
      being_solved.number_of_pieces[Black][p] = 0;
    }
  }

  being_solved.king_square[Black] = store->rn_sic;
  being_solved.king_square[White] = store->rb_sic;

  {
    unsigned int i;
    for (i = 0; i<nr_squares_on_board; i++)
      switch (store->e[i])
      {
        case Empty:
          empty_square(boardnum[i]);
          break;

        case Invalid:
          block_square(boardnum[i]);
          break;

        default:
        {
          Side const side = TSTFLAG(store->spec[i],White) ? White : Black;
          ++being_solved.number_of_pieces[side][store->e[i]];
          occupy_square(boardnum[i],store->e[i],store->spec[i]);
          break;
        }
      }
  }
}

void remember_to_keep_rider_line_open(square from, square to,
                                      int dir, int delta)
{
  square s;

  TraceFunctionEntry(__func__);
  TraceSquare(from);
  TraceSquare(to);
  TraceFunctionParam("%d",dir);
  TraceFunctionParam("%d",delta);
  TraceFunctionParamListEnd();

  for (s = from+dir; s!=to; s+=dir)
  {
    /*assert(is_square_empty(s)); doesn't work if there are holes! */
    // TODO does this overflow work on all implementations?
    assert(abs(delta)==1);
    assert(nr_reasons_for_staying_empty[s]>0 || delta>0);
    nr_reasons_for_staying_empty[s] += (unsigned int)delta;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
/* Detrmine whether some line is empty
 * @param start start of line
 * @param end end of line
 * @param dir direction from start to end
 * @return true iff the line is empty
 */
boolean is_line_empty(square start, square end, int dir)
{
  boolean result = true;
  square s;

  TraceFunctionEntry(__func__);
  TraceSquare(start);
  TraceSquare(end);
  TraceFunctionParam("%d",dir);
  TraceFunctionParamListEnd();

  for (s = start+dir; s!=end; s += dir)
    if (!is_square_empty(s))
    {
      result = false;
      break;
    }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

boolean black_pawn_attacks_king(square from)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceSquare(from);
  TraceFunctionParamListEnd();

  assert(!TSTFLAG(sq_spec(from),BlPromSq));
  assert(!TSTFLAG(sq_spec(from),BlBaseSq));

  if (being_solved.king_square[White]==initsquare)
    result = false;
  else
  {
    int const diff = being_solved.king_square[White]-from;
    result = diff==dir_down+dir_right || diff==dir_down+dir_left;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/*#define DETAILS*/
#if defined(DETAILS)
static void trace_target_position(PIECE const position[MaxPieceId+1],
                                  unsigned int nr_required_captures)
{
  unsigned int moves_per_side[nr_sides] = { 0, 0 };
  square const *bnp;

  for (bnp = boardnum; *bnp!=initsquare; bnp++)
    if (!is_square_empty(*bnp))
    {
      Flags const sp = being_solved.spec[*bnp];
      PieceIdType const id = GetPieceId(sp);
      PIECE const * const target = &position[id];
      if (target->diagram_square!=/* vide */ Empty /* TODO: Is Empty the correct value here? */)
      {
        Side const cur_side = TSTFLAG(being_solved.spec[*bnp],White) ? White : Black;
        unsigned int const time = intelligent_count_nr_of_moves_from_to_no_check(cur_side,
                                                                     get_walk_of_piece_on_square(*bnp),
                                                                     *bnp,
                                                                     target->type,
                                                                     target->diagram_square);
        moves_per_side[cur_side] += time;
        TraceWalk(get_walk_of_piece_on_square(*bnp));
        TraceSquare(*bnp);
        TraceWalk(target->type);
        TraceSquare(target->diagram_square);
        TraceEnumerator(piece_usage,target->usage);
        TraceValue("%u",time);
        TraceEOL();
      }
    }

  TraceValue("%u",nr_required_captures);
  TraceValue("%u",moves_per_side[Black]);
  TraceValue("%u",moves_per_side[White]);
  TraceEOL();
}

static piece_usage find_piece_usage(PieceIdType id)
{
  piece_usage result = piece_is_unused;

  unsigned int i;
  for (i = 0; i<MaxPiece[White]; ++i)
    if (id==GetPieceId(white[i].flags))
    {
      result = white[i].usage;
      break;
    }
  for (i = 0; i<MaxPiece[Black]; ++i)
    if (id==GetPieceId(black[i].flags))
    {
      result = black[i].usage;
      break;
    }

  assert(result!=piece_is_unused);

  return result;
}
#endif

static square PositionInDiagram_to_square(int pos)
{
  pos -= 200;
  return (square) (((pos / 24) * 8) + (pos % 24));
} 

static square orig_square_of_piece(Flags const flags)
{
  return PositionInDiagram_to_square(GetPositionInDiagram(flags));
}

typedef struct {
  piece_walk_type piece;
  Side color;
  square orig_square;
} piece_on_square;

static int get_blocking_pieces_up(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) + 8);
  for (int sq = adjacent; sq < nr_squares_on_board; sq += 8)
  {
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Queen:
      case Rook:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Rook:
            break;
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_down(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) - 8);
  for (int sq = adjacent; sq >= 0; sq -= 8)
  {
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Queen:
      case Rook:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Rook:
            break;
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_left(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) - 1);
  for (int sq = square_checked; (sq % 8);)
  {
    --sq;
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Queen:
      case Rook:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Rook:
            break;
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_right(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) + 1);
  for (int sq = adjacent; (sq % 8); ++sq)
  {
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Queen:
      case Rook:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Rook:
            break;
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_upper_left(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) + 7);
  for (int sq = adjacent; sq < nr_squares_on_board; sq += 7)
  {
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Queen:
      case Bishop:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Bishop:
            break;
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_upper_right(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) + 9);
  for (int sq = adjacent; sq < nr_squares_on_board; sq += 9)
  {
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Queen:
      case Bishop:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Bishop:
            break;
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_lower_left(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) - 9);
  for (int sq = adjacent; sq >= 0; sq -= 9)
  {
    if ((sq % 8) == 7)
      break;
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Pawn:
        return (((sq == adjacent) && (color_checked == Black)) ? -1 : 0);
      case Queen:
      case Bishop:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Bishop:
            break;
          case Pawn:
            if ((sq == adjacent) && (color_checked == Black))
              break;
            // intentional fall-through
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int get_blocking_pieces_lower_right(stored_position_type const * const store, unsigned long long const square_must_remain_open, piece_on_square const * const final, square * const blocks, square const square_checked, Side const color_checked)
{
  int num_possible_blocks = 0;
  square possible_blocks[7];
  int const adjacent = (((int) square_checked) - 7);
  for (int sq = adjacent; sq >= 0; sq -= 7)
  {
    if (!(sq % 8))
      break;
    if (final[sq].color == color_checked)
      return 0;
    switch (final[sq].piece)
    {
      case Empty:
        break;
      case King:
        return ((sq == adjacent) ? -1 : 0);
      case Pawn:
        return (((sq == adjacent) && (color_checked == Black)) ? -1 : 0);
      case Queen:
      case Bishop:
        if (!num_possible_blocks)
          return -1;
        for (int i = 0; i < num_possible_blocks; ++i)
          blocks[i] = possible_blocks[i];
        return num_possible_blocks;
      default:
        return 0;
    }
    if (!((square_must_remain_open >> sq) & 1U))
      if (TSTFLAG(store->spec[sq], White))
        switch (store->e[sq])
        {
          case Empty:
          case Queen:
          case Bishop:
            break;
          case Pawn:
            if ((sq == adjacent) && (color_checked == Black))
              break;
            // intentional fall-through
          default:
            possible_blocks[num_possible_blocks++] = (square) sq;
        }
  }
  return 0;
}

static int num_knight_checks(piece_on_square const * const final, square const square_checked, Side const color_checked)
{
  int const row = (square_checked / 8);
  int const col = (square_checked % 8);
  int num_checks = 0;
  if (row)
  {
    if (col > 1)
      if ((final[square_checked - 10].piece == Knight) && (final[square_checked - 10].color != color_checked))
        ++num_checks;
    if (col < 6)
      if ((final[square_checked - 6].piece == Knight) && (final[square_checked - 6].color != color_checked))
        ++num_checks;
    if (row > 1)
    {
      if (col)
        if ((final[square_checked - 17].piece == Knight) && (final[square_checked - 17].color != color_checked))
          ++num_checks;
      if (col < 7)
        if ((final[square_checked - 15].piece == Knight) && (final[square_checked - 15].color != color_checked))
          ++num_checks;
    }
  }
  if (row < 7)
  {
    if (col > 1)
      if ((final[square_checked + 6].piece == Knight) && (final[square_checked + 6].color != color_checked))
        ++num_checks;
    if (col < 6)
      if ((final[square_checked + 10].piece == Knight) && (final[square_checked + 10].color != color_checked))
        ++num_checks;
    if (row < 6)
    {
      if (col)
        if ((final[square_checked + 15].piece == Knight) && (final[square_checked + 15].color != color_checked))
          ++num_checks;
      if (col < 7)
        if ((final[square_checked + 17].piece == Knight) && (final[square_checked + 17].color != color_checked))
          ++num_checks;
    }
  }
  return num_checks;
}

static piece_on_square target_before_white_move[nr_squares_on_board];
static int num_extra_blocks_needed_to_protect_white;
static int num_extra_blocks_needed_to_protect_black;
static square extra_blocks_to_protect_white[8][6]; // first index = line, second index = possibility along that line
static square extra_blocks_to_protect_black[8][6]; // first index = line, second index = possibility along that line
static int num_extra_block_poss_to_protect_white[8];
static int num_extra_block_poss_to_protect_black[8];
static int num_unblockable_checks_of_white;
static boolean castle_kingside;
static boolean castle_queenside;

static boolean get_target_before_white_move(stored_position_type const * const store)
{
  enum {
    a1, b1, c1, d1, e1, f1, g1, h1,
    a2, b2, c2, d2, e2, f2, g2, h2,
    a3, b3, c3, d3, e3, f3, g3, h3,
    a4, b4, c4, d4, e4, f4, g4, h4,
    a5, b5, c5, d5, e5, f5, g5, h5,
    a6, b6, c6, d6, e6, f6, g6, h6,
    a7, b7, c7, d7, e7, f7, g7, h7,
    a8, b8, c8, d8, e8, f8, g8, h8
  };

  // Convert the position to a more convenient form.
  unsigned long long seen_black_pieces = 0;
  square bKPosition = nr_squares_on_board;
  square wKPosition = nr_squares_on_board;
  for (int index = a1; index <= h8; ++index)
  {
    target_before_white_move[index].piece = Empty;
    target_before_white_move[index].color = no_side;
    target_before_white_move[index].orig_square = nr_squares_on_board;
  }
  for (PieceIdType id = 0; id <= MaxPieceId; ++id)
  {
    square const diagram_square = target_position[id].diagram_square;
    if (diagram_square != initsquare)
    {
      Flags const flags = target_position[id].flags;
      square const orig_square = orig_square_of_piece(flags);
      if (orig_square > h8)
        return false;
      piece_walk_type p = target_position[id].type;
      if (p == Invalid)
        p = nr_piece_walks;
      int const index = PositionInDiagram_to_square(diagram_square);
      target_before_white_move[index].piece = p;
      target_before_white_move[index].orig_square = orig_square;
      if (TSTFLAG(flags, White))
      {
        if (p == King)
          wKPosition = index;
        target_before_white_move[index].color = White;
      }
      else
      {
        if (p == King)
          bKPosition = index;
        target_before_white_move[index].color = Black;
        seen_black_pieces |= (1ULL << orig_square);
      }
    }
  }

  // ensure that White's move was legal
  castle_kingside = false;
  castle_queenside = false;
  boolean pawn_capture = false;
  int moved_white_piece_orig_square;
  int moved_white_piece_new_square;
  unsigned long long square_must_remain_open;
  if ((wKPosition == g1) && (target_before_white_move[g1].orig_square == e1))
  {
    if ((target_before_white_move[f1].piece != Rook) || (target_before_white_move[f1].color != White) || (target_before_white_move[f1].orig_square != h1))
      return false;
    if ((target_before_white_move[e1].piece != Empty) || (target_before_white_move[h1].piece != Empty))
      return false;
    castle_kingside = true;
    moved_white_piece_orig_square = e1;
    moved_white_piece_new_square = g1;
    square_must_remain_open = ((1ULL << f1) | (1ULL << g1));
  }
  else if ((wKPosition == c1) && (target_before_white_move[c1].orig_square == e1))
  {
    if ((target_before_white_move[d1].piece != Rook) || (target_before_white_move[d1].color != White) || (target_before_white_move[d1].orig_square != a1))
      return false;
    if ((target_before_white_move[a1].piece != Empty) || (target_before_white_move[b1].piece != Empty) || (target_before_white_move[e1].piece != Empty))
      return false;
    castle_queenside = true;
    moved_white_piece_orig_square = e1;
    moved_white_piece_new_square = c1;
    square_must_remain_open = ((1ULL << b1) | (1ULL << c1) | (1ULL << d1));
  }
  else
  {
    square_must_remain_open = 0;
    for (int index = a1; index <= h8; ++index)
    {
      if (target_before_white_move[index].color == White)
      {
        int orig_square = target_before_white_move[index].orig_square;
        if (orig_square != index)
        {
          // the square White moves from must be empty
          if (target_before_white_move[orig_square].piece != Empty)
            return false;

          moved_white_piece_orig_square = orig_square;
          moved_white_piece_new_square = index;

          // a White line piece can't have jumped over anything
          piece_walk_type const p = store->e[orig_square];
          if (p != Knight)
          {
            // line pieces cannot have jumped over anything
            int orig_rank = (orig_square / 8);
            int orig_file = (orig_square % 8);
            int const new_rank = (index / 8);
            int const new_file = (index % 8);
            int step;
            if (new_rank > orig_rank)
              step = 8;
            else if (new_rank < orig_rank)
              step = -8;
            else
              step = 0;
            if (new_file > orig_file)
              ++step;
            else if (new_file < orig_file)
              --step;
            while ((orig_square += step) != index)
            {
              if (target_before_white_move[orig_square].piece != Empty)
                return false;
              square_must_remain_open |= (1ULL << orig_square);
            }
          }
          goto FOUND_MOVED_WHITE_PIECE;
        }
      }
    }
    // White must have made exactly one move, but we didn't find ANY moves.
    return false;
FOUND_MOVED_WHITE_PIECE:;
  }

  // retract White's last move
  target_before_white_move[moved_white_piece_orig_square].piece = store->e[moved_white_piece_orig_square];
  target_before_white_move[moved_white_piece_orig_square].color = White;
  target_before_white_move[moved_white_piece_orig_square].orig_square = orig_square_of_piece(store->spec[moved_white_piece_orig_square]);
  target_before_white_move[moved_white_piece_new_square].piece = Empty;
  target_before_white_move[moved_white_piece_new_square].color = no_side;
  target_before_white_move[moved_white_piece_new_square].orig_square = nr_squares_on_board;
  if (target_before_white_move[moved_white_piece_orig_square].piece == King)
    wKPosition = moved_white_piece_orig_square;
  if (castle_kingside)
  {
    target_before_white_move[h1].piece = Rook;
    target_before_white_move[h1].color = White;
    target_before_white_move[h1].orig_square = h1;
    target_before_white_move[f1].piece = Empty;
    target_before_white_move[f1].color = no_side;
    target_before_white_move[f1].orig_square = nr_squares_on_board;
  }
  else if (castle_queenside)
  {
    target_before_white_move[a1].piece = Rook;
    target_before_white_move[a1].color = White;
    target_before_white_move[a1].orig_square = a1;
    target_before_white_move[d1].piece = Empty;
    target_before_white_move[d1].color = no_side;
    target_before_white_move[d1].orig_square = nr_squares_on_board;
  }
  else if ((target_before_white_move[moved_white_piece_orig_square].piece == Pawn) &&
           ((moved_white_piece_new_square - moved_white_piece_orig_square) % 8))
    pawn_capture = true;
  boolean found_capture = false;
  for (int index = a1; index <= h8; ++index)
  {
    if (TSTFLAG(store->spec[index], Black))
    {
      square const orig_square = orig_square_of_piece(store->spec[index]);
      if (!((seen_black_pieces >> orig_square) & 1U))
      {
        if (found_capture)
          return false;

        // some moves can't be captures
        if (castle_kingside || castle_queenside)
          return false;
        if ((target_before_white_move[moved_white_piece_orig_square].piece == Pawn) && !pawn_capture)
          return false;

        if (store->e[index] == Pawn)
          target_before_white_move[moved_white_piece_new_square].piece = nr_piece_walks; // The pawn might have promoted.
        else
          target_before_white_move[moved_white_piece_new_square].piece = store->e[index];
        target_before_white_move[moved_white_piece_new_square].color = Black;
        target_before_white_move[moved_white_piece_new_square].orig_square = orig_square;
        found_capture = true;
      }
    }
  }
  if (!found_capture)
  {
    if (pawn_capture)
      return false;
    square_must_remain_open |= (1ULL << moved_white_piece_new_square);
  }
  // TODO: Should we consider the possibility that White's move was an en passant capture justified by retrograde analysis?

  num_unblockable_checks_of_white = num_knight_checks(target_before_white_move, wKPosition, White);
  if (num_unblockable_checks_of_white > 1)
    return false; // There can be at most one Knight check.
    

  // Restore whatever White pieces are needed to block checks.
  num_extra_blocks_needed_to_protect_white = 0;
  int direction_of_previous_line_check = 8;

  int num_blocks_tmp = get_blocking_pieces_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      direction_of_previous_line_check = 0;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }
  num_blocks_tmp = get_blocking_pieces_upper_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      direction_of_previous_line_check = 1;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }
  num_blocks_tmp = get_blocking_pieces_up(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      if (direction_of_previous_line_check < 1)
        return false;
      direction_of_previous_line_check = 2;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }
  num_blocks_tmp = get_blocking_pieces_upper_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      if (direction_of_previous_line_check < 2)
        return false;
      direction_of_previous_line_check = 3;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }  
  num_blocks_tmp = get_blocking_pieces_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      if (direction_of_previous_line_check < 3)
        return false;
      direction_of_previous_line_check = 4;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }
  num_blocks_tmp = get_blocking_pieces_lower_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      if (direction_of_previous_line_check < 4)
        return false;
      direction_of_previous_line_check = 5;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }
  num_blocks_tmp = get_blocking_pieces_down(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      if (direction_of_previous_line_check < 5)
        return false;
      direction_of_previous_line_check = 6;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }
  num_blocks_tmp = get_blocking_pieces_lower_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], wKPosition, White);
  switch (num_blocks_tmp)
  {
    case -1:
      if (num_unblockable_checks_of_white > 1)
        return false; // There can be at most 2 checks of White at a time.
      if (direction_of_previous_line_check < 6)
        return false;
      ++num_unblockable_checks_of_white;
      break;
    case 0:
      break;
    default:
      num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
  }

  if (num_unblockable_checks_of_white && (castle_kingside || castle_queenside))
    // If White castled, no checks are allowed.
    return false;

  if ((num_unblockable_checks_of_white == 2) || castle_kingside || castle_queenside)
    // We have to block all the other checks.
    for (int i = 0; i < num_extra_blocks_needed_to_protect_white;)
    {
      int num_poss = num_extra_block_poss_to_protect_white[i];
      if (num_poss == 1)
      {
        // Add this blocker and remove it from the set.
        square const blocking_square = extra_blocks_to_protect_white[i][0];
        target_before_white_move[blocking_square].piece = store->e[blocking_square];
        target_before_white_move[blocking_square].color = White;
        target_before_white_move[blocking_square].orig_square = orig_square_of_piece(store->spec[blocking_square]);
        --num_extra_blocks_needed_to_protect_white;
        if (i < num_extra_blocks_needed_to_protect_white)
        {
          num_poss = num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white];
          num_extra_block_poss_to_protect_white[i] = num_poss;
          for (int j = 0; j < num_poss; ++j)
            extra_blocks_to_protect_white[i][j] = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][j];
        }
      }
      else
        ++i;
      // TODO: consider blocks when num_extra_block_poss_to_protect_white[i] > 1 ?
    }
  // TODO: If num_unblockable_checks_of_white == 2, ensure that they're a possible double-check.

  // If White castled, no checks are allowed and the square the King crossed over also can't have been attacked.
  if (castle_kingside)
  {
    if (num_knight_checks(target_before_white_move, f1, White))
      return false;      
    num_blocks_tmp = get_blocking_pieces_upper_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], f1, White);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_up(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], f1, White);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_upper_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], f1, White);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
    }
  }
  else if (castle_queenside)
  {
    if (num_knight_checks(target_before_white_move, d1, White))
      return false;
    num_blocks_tmp = get_blocking_pieces_upper_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], d1, White);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_up(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], d1, White);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_upper_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white], d1, White);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_white[num_extra_blocks_needed_to_protect_white][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_white[num_extra_blocks_needed_to_protect_white++] = num_blocks_tmp;
    }
  }

  // Black can't have been in check.
  num_extra_blocks_needed_to_protect_black = 0;
  if (bKPosition != nr_squares_on_board)
  {
    if (num_knight_checks(target_before_white_move, bKPosition, Black))
      return false;
    num_blocks_tmp = get_blocking_pieces_up(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_upper_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_lower_right(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_down(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_lower_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
    num_blocks_tmp = get_blocking_pieces_upper_left(store, square_must_remain_open, target_before_white_move, extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black], bKPosition, Black);
    switch (num_blocks_tmp)
    {
      case -1:
        return false;
      case 0:
        break;
      case 1:
        {
          square const block_square = extra_blocks_to_protect_black[num_extra_blocks_needed_to_protect_black][0];
          target_before_white_move[block_square].piece = store->e[block_square];
          target_before_white_move[block_square].color = White;
          target_before_white_move[block_square].orig_square = orig_square_of_piece(store->spec[block_square]);
        }
        break;
      default:
        num_extra_block_poss_to_protect_black[num_extra_blocks_needed_to_protect_black++] = num_blocks_tmp;
    }
  }
  // TODO: Can/Should we add these extra blockers to target_position?

  return true;
}

boolean target_position_is_ser_h_feasible(boolean const first_move)
{
  enum {
    a1, b1, c1, d1, e1, f1, g1, h1,
    a2, b2, c2, d2, e2, f2, g2, h2,
    a3, b3, c3, d3, e3, f3, g3, h3,
    a4, b4, c4, d4, e4, f4, g4, h4,
    a5, b5, c5, d5, e5, f5, g5, h5,
    a6, b6, c6, d6, e6, f6, g6, h6,
    a7, b7, c7, d7, e7, f7, g7, h7,
    a8, b8, c8, d8, e8, f8, g8, h8
  };

  if (castle_kingside)
  {
    if (TSTCASTLINGFLAGMASK(White, k_castling) != k_castling)
      return false;
  }
  else if (castle_queenside)
  {
    if (TSTCASTLINGFLAGMASK(White, q_castling) != q_castling)
      return false;
  }

  // Convert the positions to more convenient forms.
  piece_on_square initial[nr_squares_on_board];
  piece_on_square final[nr_squares_on_board];
  square wKPosition = nr_squares_on_board;
  square cur_square_of_piece[nr_squares_on_board];
  for (int index = a1; index <= h8; ++index)
    cur_square_of_piece[index] = nr_squares_on_board;
  for (int index = a1; index <= h8; ++index)
  {
    square const cur_square = boardnum[index];
    piece_walk_type p = get_walk_of_piece_on_square(cur_square);
    if (p == Invalid)
      p = nr_piece_walks;
    initial[index].piece = p;
    if (p == Empty)
    {
      initial[index].color = no_side;
      initial[index].orig_square = nr_squares_on_board;
    }
    else
    {
      Flags const flags = being_solved.spec[cur_square];
      if (TSTFLAG(flags, White))
      {
        if (p == King)
          wKPosition = index;
        initial[index].color = White;
      }
      else
        initial[index].color = Black;
      square const orig_square = orig_square_of_piece(flags);
      initial[index].orig_square = orig_square;
      cur_square_of_piece[orig_square] = index;
    }

    final[index] = target_before_white_move[index];
    if ((final[index].color == White) && (initial[index].color != White))
      return false;
  }

  // Restore whatever additional White pieces are needed to block checks.
  if ((num_unblockable_checks_of_white == 2) || castle_kingside || castle_queenside)
    // We have to block all the other checks.
    for (int i = 0; i < num_extra_blocks_needed_to_protect_white; ++i)
    {
      int const num_poss = num_extra_block_poss_to_protect_white[i];
      int num_new_poss = 0;
      square new_poss[6];
      for (int j = 0; j < num_poss; ++j)
      {
        int const block_sq = extra_blocks_to_protect_white[i][j];
        if (initial[block_sq].color == White)
          new_poss[num_new_poss++] = block_sq;
      }
      if (!num_new_poss)
        return false;
      if (num_new_poss == 1)
        final[new_poss[0]] = initial[new_poss[0]];
      // TODO: consider blocks when num_new_poss > 1 ?
    }
    // TODO: Consider that these added pieces might check Black.

  for (int i = 0; i < num_extra_blocks_needed_to_protect_black; ++i)
  {
    int const num_poss = num_extra_block_poss_to_protect_black[i];
    int num_new_poss = 0;
    square new_poss[6];
    for (int j = 0; j < num_poss; ++j)
    {
      int const block_sq = extra_blocks_to_protect_black[i][j];
      if (initial[block_sq].color == White)
        new_poss[num_new_poss++] = block_sq;
    }
    if (!num_new_poss)
      return false;
    if (num_new_poss == 1)
      final[new_poss[0]] = initial[new_poss[0]];
    // TODO: consider blocks when num_new_poss > 1 ?
  }
  // TODO: If num_unblockable_checks_of_white == 2, ensure that they're a possible double-check.

  // What squares have White's pieces guarded throughout?
  unsigned long long guarded_by_white = 0;
  for (int sq = a1; sq <= h8; ++sq)
    if (final[sq].color == White)
    {
      int const row = (sq / 8);
      int const col = (sq % 8);
      piece_walk_type const p = final[sq].piece;
      switch (final[sq].piece)
      {
        case Pawn:
          if (col)
            guarded_by_white |= (1ULL << (sq + 7));
          if (col < 7)
            guarded_by_white |= (1ULL << (sq + 9));
          break;
        case Knight:
          if (row)
          {
            if (col > 1)
              guarded_by_white |= (1ULL << (sq - 10));
            if (col < 6)
              guarded_by_white |= (1ULL << (sq - 6));
            if (row > 1)
            {
              if (col)
                guarded_by_white |= (1ULL << (sq - 17));
              if (col < 7)
                guarded_by_white |= (1ULL << (sq - 15));
            }
          }
          if (row < 7)
          {
            if (col > 1)
              guarded_by_white |= (1ULL << (sq + 6));
            if (col < 6)
              guarded_by_white |= (1ULL << (sq + 10));
            if (row < 6)
            {
              if (col)
                guarded_by_white |= (1ULL << (sq + 15));
              if (col < 7)
                guarded_by_white |= (1ULL << (sq + 17));
            }
          }
          break;
        case Queen:
        case King:
        case Bishop:
          if (row)
          {
            if (col)
              guarded_by_white |= (1ULL << (sq - 9));
            if (col < 7)
              guarded_by_white |= (1ULL << (sq - 7));
          }
          if (row < 7)
          {
            if (col)
              guarded_by_white |= (1ULL << (sq + 7));
            if (col < 7)
              guarded_by_white |= (1ULL << (sq + 9));
          }
          if (p == Bishop)
            break;
          // intentional fall-through
        case Rook:
          if (row)
            guarded_by_white |= (1ULL << (sq - 8));
          if (row < 7)
            guarded_by_white |= (1ULL << (sq + 8));
          if (col)
            guarded_by_white |= (1ULL << (sq - 1));
          if (col < 7)
            guarded_by_white |= (1ULL << (sq + 1));
          break;
        case Dummy:
          break;
        default:
          assert(0);
          return false;
      }
    }

  // What squares must attack the wK?
  unsigned long long rook_checks_white_king = 0;
  unsigned long long knight_checks_white_king = 0;
  unsigned long long pawn_checks_white_king = 0;
  unsigned long long bishop_checks_white_king = 0;
  unsigned long long queen_checks_white_king = 0;
  if (wKPosition != nr_squares_on_board)
  {
    int const wKRow = (wKPosition / 8);
    int const wKCol = (wKPosition % 8);
    if (wKRow)
    {
      rook_checks_white_king |= (1ULL << (wKPosition - 8));
      if (wKCol)
      {
        bishop_checks_white_king |= (1ULL << (wKPosition - 9));
        if (wKCol > 1)
          knight_checks_white_king |= (1ULL << (wKPosition - 10));
      }
      if (wKCol < 7)
      {
        bishop_checks_white_king |= (1ULL << (wKPosition - 7));
        if (wKCol < 6)
          knight_checks_white_king |= (1ULL << (wKPosition - 6));
      }
      if (wKRow > 1)
      {
        if (wKCol)
          knight_checks_white_king |= (1ULL << (wKPosition - 17));
        if (wKCol < 7)
          knight_checks_white_king |= (1ULL << (wKPosition - 15));
      }
    }
    if (wKRow < 7)
    {
      rook_checks_white_king |= (1ULL << (wKPosition + 8));
      if (wKCol)
      {
        pawn_checks_white_king |= (1ULL << (wKPosition + 7));
        if (wKCol > 1)
          knight_checks_white_king |= (1ULL << (wKPosition + 6));
      }
      if (wKCol < 7)
      {
        pawn_checks_white_king |= (1ULL << (wKPosition + 9));
        if (wKCol < 6)
          knight_checks_white_king |= (1ULL << (wKPosition + 10));
      }
      if (wKRow < 6)
      {
        if (wKCol)
          knight_checks_white_king |= (1ULL << (wKPosition + 15));
        if (wKCol < 7)
          knight_checks_white_king |= (1ULL << (wKPosition + 17));
      }
    }
    if (wKCol)
    {
      rook_checks_white_king |= (1ULL << (wKPosition - 1));
    }
    if (wKCol < 7)
    {
      rook_checks_white_king |= (1ULL << (wKPosition + 1));
    }
    bishop_checks_white_king |= pawn_checks_white_king;
    queen_checks_white_king = (bishop_checks_white_king | rook_checks_white_king);
  }

  // Determine which pieces never moved.
  unsigned long long piece_never_moved = 0;
  for (int index = a1; index <= h8; ++index)
    if ((final[index].color == White) ||
        ((final[index].piece == Pawn) && (final[index].orig_square == index)))
      piece_never_moved |= (1ULL << index);
  unsigned long long prev_piece_never_moved;
  do {
    prev_piece_never_moved = piece_never_moved;
    for (int index = a1; index <= h8; ++index)
    {
      piece_walk_type const p = initial[index].piece;
      if (p != Empty)
      {
        unsigned long long checking_squares;
        switch (p)
        {
          case Pawn:
            checking_squares = pawn_checks_white_king;
            break;
          case Knight:
            checking_squares = knight_checks_white_king;
            break;
          case Bishop:
            checking_squares = bishop_checks_white_king;
            break;
          case Rook:
            checking_squares = rook_checks_white_king;
            break;
          case King:
          case Queen:
            checking_squares = queen_checks_white_king;
            break;
          case Dummy:
            checking_squares = 0;
            break;
          default:
            assert(0);
            return false;
        }
        if (!(((piece_never_moved | checking_squares) >> index) & 1U))
        {
          int const row = (index / 8);
          int const col = (index % 8);
          switch (p)
          {
            case Pawn:
              {
                int new_pos = (index - 8);
                if (!((piece_never_moved >> new_pos) & 1U))
                {
                  if (!((checking_squares >> new_pos) & 1U))
                    break;
                  if (row == 6)
                    if (!(((piece_never_moved | checking_squares) >> (new_pos - 8)) & 1U))
                      break;
                }
                if (col)
                {
                  new_pos = (index - 9);
                  if (!((checking_squares >> new_pos) & 1U))
                  {
                    if ((initial[new_pos].color == White) &&
                        !((piece_never_moved >> new_pos) & 1U))
                      break;
                    if (row == 3)
                    {
                      int const en_passant = (index - 1);
                      if ((initial[en_passant].piece == Pawn) &&
                          (initial[en_passant].color == White) &&
                          (initial[en_passant - 8].piece == Empty) &&
                          (initial[en_passant - 16].piece == Empty) &&
                          !((piece_never_moved >> en_passant) & 1U))
                        break;
                    }
                  }
                }
                if (col < 7)
                {
                  new_pos = (index - 7);
                  if (!((checking_squares >> new_pos) & 1U))
                  {
                    if ((initial[new_pos].color == White) &&
                        !((piece_never_moved >> new_pos) & 1U))
                      break;
                    if (row == 3)
                    {
                      int const en_passant = (index + 1);
                      if ((initial[en_passant].piece == Pawn) &&
                          (initial[en_passant].color == White) &&
                          (initial[en_passant - 8].piece == Empty) &&
                          (initial[en_passant - 16].piece == Empty) &&
                          !((piece_never_moved >> en_passant) & 1U))
                        break;
                    }
                  }
                }
              }
              piece_never_moved |= (1ULL << index);
              break;
            case Knight:
              {
                unsigned long long const forbidden_squares = (piece_never_moved | checking_squares);
                if (row)
                {
                  if (col > 1)
                    if (!((forbidden_squares >> (index - 10)) & 1U))
                      break;
                  if (col < 6)
                    if (!((forbidden_squares >> (index - 6)) & 1U))
                      break;
                  if (row > 1)
                  {
                    if (col)
                      if (!((forbidden_squares >> (index - 17)) & 1U))
                        break;
                    if (col < 7)
                      if (!((forbidden_squares >> (index - 15)) & 1U))
                        break;
                  }
                }
                if (row < 7)
                {
                  if (col > 1)
                    if (!((forbidden_squares >> (index + 6)) & 1U))
                      break;
                  if (col < 6)
                    if (!((forbidden_squares >> (index + 10)) & 1U))
                      break;
                  if (row < 6)
                  {
                    if (col)
                      if (!((forbidden_squares >> (index + 15)) & 1U))
                        break;
                    if (col < 7)
                      if (!((forbidden_squares >> (index + 17)) & 1U))
                        break;
                  }
                }
              }
              piece_never_moved |= (1ULL << index);
              break;
            case King:
              {
                unsigned long long const forbidden_squares = (piece_never_moved | guarded_by_white);
                if (row)
                {
                  if (!((forbidden_squares >> (index - 8)) & 1U))
                    break;
                  if (col)
                    if (!((forbidden_squares >> (index - 9)) & 1U))
                      break;
                  if (col < 7)
                    if (!((forbidden_squares >> (index - 7)) & 1U))
                      break;
                }
                if (row < 7)
                {
                  if (!((forbidden_squares >> (index + 8)) & 1U))
                    break;
                  if (col)
                    if (!((forbidden_squares >> (index + 7)) & 1U))
                      break;
                  if (col < 7)
                    if (!((forbidden_squares >> (index + 9)) & 1U))
                      break;
                }
                if (col)
                  if (!((forbidden_squares >> (index - 1)) & 1U))
                    break;
                if (col < 7)
                  if (!((forbidden_squares >> (index + 1)) & 1U))
                    break;
              }
              piece_never_moved |= (1ULL << index);
              break;
            case Queen:
            case Bishop:
              for (int poss_move = (index + 9); ((poss_move <= h8) && (poss_move % 8)); poss_move += 9)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_BISHOP_MOVE;
              }
              for (int poss_move = (index - 9); ((poss_move >= (int) a1) && ((poss_move % 8) != 7)); poss_move -= 9)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_BISHOP_MOVE;
              }
              for (int poss_move = (index - 7); ((poss_move >= (int) a1) && (poss_move % 8)); poss_move -= 7)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_BISHOP_MOVE;
              }
              for (int poss_move = (index + 7); ((poss_move <= h8) && (poss_move % 8)); poss_move += 7)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_BISHOP_MOVE;
              }
              if (p == Bishop)
              {
                piece_never_moved |= (1ULL << index);
FOUND_BISHOP_MOVE:
                break;
              }
              // intentional fall-through
            case Rook:
              for (int poss_move = (index + 8); poss_move <= h8; poss_move += 8)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_ROOK_MOVE;
              }
              for (int poss_move = (index - 8); poss_move >= (int) a1; poss_move -= 8)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_ROOK_MOVE;
              }
              for (int poss_move = index; (poss_move % 8);)
              {
                --poss_move;
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_ROOK_MOVE;
              }
              for (int poss_move = (index + 1); (poss_move % 8); ++poss_move)
              {
                if ((piece_never_moved >> poss_move) & 1U)
                  break;
                if (!((checking_squares >> poss_move) & 1U))
                  goto FOUND_ROOK_MOVE;
              }
              piece_never_moved |= (1ULL << index);
FOUND_ROOK_MOVE:
              break;
            case Dummy:
              piece_never_moved |= (1ULL << index);
              break;
            default:
              assert(0);
              return false;
          }
        }
      }
    }
  } while (prev_piece_never_moved != piece_never_moved);

  // Where could pieces end up?
  unsigned long long pawn_could_reach[nr_squares_on_board + 1];
  unsigned long long knight_could_reach[nr_squares_on_board + 1];
  unsigned long long bishop_could_reach[nr_squares_on_board + 1];
  unsigned long long rook_could_reach[nr_squares_on_board + 1];
  unsigned long long queen_could_reach[nr_squares_on_board + 1];
  unsigned long long king_could_reach[nr_squares_on_board + 1];
  for (int index = a1; index <= h8; ++index)
  {
    unsigned long long cur_bit = (1ULL << index);
    pawn_could_reach[index] = cur_bit;
    knight_could_reach[index] = cur_bit;
    bishop_could_reach[index] = cur_bit;
    rook_could_reach[index] = cur_bit;
    queen_could_reach[index] = cur_bit;
    if ((guarded_by_white >> index) & 1U)
      king_could_reach[index] = 0;
    else
      king_could_reach[index] = cur_bit;
  }
  // Where could pawns end up?
  for (int row = 1; row < 7; ++row)
  {
    for (int col = 0; col < 8; ++col)
    {
      int const index = ((row * 8) + col);
      if (!((pawn_checks_white_king >> index) & 1U))
      {
        if (!((piece_never_moved >> (index - 8)) & 1U))
        {
          pawn_could_reach[index] |= pawn_could_reach[index - 8];
          if (row == 6)
            if (!((piece_never_moved >> (index - 16)) & 1U))
              pawn_could_reach[index] |= pawn_could_reach[index - 16];
        }
        if (col)
          if ((initial[index - 9].color == White) && !((piece_never_moved >> (index - 9)) & 1U))
            pawn_could_reach[index] |= pawn_could_reach[index - 9];
        if (col < 7)
          if ((initial[index - 7].color == White) && !((piece_never_moved >> (index - 7)) & 1U))
            pawn_could_reach[index] |= pawn_could_reach[index - 7];
      }
    }
  }
  // Handle an initial en passant capture.
  if (first_move)
    for (int index = a4; index <= h4; ++index)
      if ((initial[index].piece == Pawn) && (initial[index].color == Black) && !((pawn_checks_white_king >> index) & 1U))
      {
        if (index > a4)
          if ((initial[index - 1].piece == Pawn) &&
              (initial[index - 1].color == White) &&
              (initial[index - 9].piece == Empty) &&
              (initial[index - 17].piece == Empty) &&
              !((piece_never_moved >> (index - 1)) & 1U))
            pawn_could_reach[index] |= pawn_could_reach[index - 9];
        if (index < h4)
          if ((initial[index + 1].piece == Pawn) &&
              (initial[index + 1].color == White) &&
              (initial[index - 7].piece == Empty) &&
              (initial[index - 15].piece == Empty) &&
              !((piece_never_moved >> (index + 1)) & 1U))
            pawn_could_reach[index] |= pawn_could_reach[index - 7];
      }

  // Where could Knights end up?
  boolean found_another_move;
  do {
    found_another_move = false;
    for (int index = a1; index <= h8; ++index)
      if (!((knight_checks_white_king >> index) & 1U))
      {
        unsigned long long orig_poss = knight_could_reach[index];
        int const row = (index / 8);
        int const col = (index % 8);
        if (row)
        {
          if (col > 1)
            if (!((piece_never_moved >> (index - 10)) & 1U))
              knight_could_reach[index] |= knight_could_reach[index - 10];
          if (col < 6)
            if (!((piece_never_moved >> (index - 6)) & 1U))
              knight_could_reach[index] |= knight_could_reach[index - 6];
          if (row > 1)
          {
            if (col)
              if (!((piece_never_moved >> (index - 17)) & 1U))
                knight_could_reach[index] |= knight_could_reach[index - 17];
            if (col < 7)
              if (!((piece_never_moved >> (index - 15)) & 1U))
                knight_could_reach[index] |= knight_could_reach[index - 15];
          }
        }
        if (row < 7)
        {
          if (col > 1)
            if (!((piece_never_moved >> (index + 6)) & 1U))
              knight_could_reach[index] |= knight_could_reach[index + 6];
          if (col < 6)
            if (!((piece_never_moved >> (index + 10)) & 1U))
              knight_could_reach[index] |= knight_could_reach[index + 10];
          if (row < 6)
          {
            if (col)
              if (!((piece_never_moved >> (index + 15)) & 1U))
                knight_could_reach[index] |= knight_could_reach[index + 15];
            if (col < 7)
              if (!((piece_never_moved >> (index + 17)) & 1U))
                knight_could_reach[index] |= knight_could_reach[index + 17];
          }
        }
        if (knight_could_reach[index] != orig_poss)
          found_another_move = true;
      }
  } while (found_another_move);

  // Where could Bishops end up?
  do
  {
    found_another_move = false;
    for (int index = a1; index <= h8; ++index)
      if (!((bishop_checks_white_king >> index) & 1U))
      {
        unsigned long long orig_poss = bishop_could_reach[index];
        for (int poss_move = (index + 9); ((poss_move <= h8) && (poss_move % 8)); poss_move += 9)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          bishop_could_reach[index] |= bishop_could_reach[poss_move];
        }
        for (int poss_move = (index - 9); ((poss_move >= (int) a1) && ((poss_move % 8) != 7)); poss_move -= 9)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          bishop_could_reach[index] |= bishop_could_reach[poss_move];
        }
        for (int poss_move = (index - 7); ((poss_move >= (int) a1) && (poss_move % 8)); poss_move -= 7)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          bishop_could_reach[index] |= bishop_could_reach[poss_move];
        }
        for (int poss_move = (index + 7); ((poss_move <= h8) && (poss_move % 8)); poss_move += 7)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          bishop_could_reach[index] |= bishop_could_reach[poss_move];
        }
        if (bishop_could_reach[index] != orig_poss)
          found_another_move = true;
      }
  } while (found_another_move);

  // Where could Rooks end up?
  do
  {
    found_another_move = false;
    for (int index = a1; index <= h8; ++index)
      if (!((rook_checks_white_king >> index) & 1U))
      {
        unsigned long long orig_poss = rook_could_reach[index];
        for (int poss_move = (index + 8); poss_move <= h8; poss_move += 8)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          rook_could_reach[index] |= rook_could_reach[poss_move];
        }
        for (int poss_move = (index - 8); poss_move >= (int) a1; poss_move -= 8)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          rook_could_reach[index] |= rook_could_reach[poss_move];
        }
        for (int poss_move = index; (poss_move % 8);)
        {
          --poss_move;
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          rook_could_reach[index] |= rook_could_reach[poss_move];
        }
        for (int poss_move = (index + 1); (poss_move % 8); ++poss_move)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          rook_could_reach[index] |= rook_could_reach[poss_move];
        }
        if (rook_could_reach[index] != orig_poss)
          found_another_move = true;
      }
  } while (found_another_move);

  // Where could Queens end up?
  do
  {
    found_another_move = false;
    for (int index = a1; index <= h8; ++index)
      if (!((queen_checks_white_king >> index) & 1U))
      {
        unsigned long long orig_poss = queen_could_reach[index];
        for (int poss_move = (index + 9); ((poss_move <= h8) && (poss_move % 8)); poss_move += 9)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = (index - 9); ((poss_move >= (int) a1) && ((poss_move % 8) != 7)); poss_move -= 9)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = (index - 7); ((poss_move >= (int) a1) && (poss_move % 8)); poss_move -= 7)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = (index + 7); ((poss_move <= h8) && (poss_move % 8)); poss_move += 7)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = (index + 8); poss_move <= h8; poss_move += 8)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = (index - 8); poss_move >= (int) a1; poss_move -= 8)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = index; (poss_move % 8);)
        {
          --poss_move;
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        for (int poss_move = (index + 1); (poss_move % 8); ++poss_move)
        {
          if ((piece_never_moved >> poss_move) & 1U)
            break;
          queen_could_reach[index] |= queen_could_reach[poss_move];
        }
        if (queen_could_reach[index] != orig_poss)
          found_another_move = true;
      }
  } while (found_another_move);

  // Where could the King end up?
  do
  {
    found_another_move = false;
    unsigned long long const forbidden_squares = (piece_never_moved | guarded_by_white);
    for (int index = a1; index <= h8; ++index)
      if (!((forbidden_squares >> index) & 1U))
      {
        unsigned long long orig_poss = king_could_reach[index];
        int const row = (index / 8);
        int const col = (index % 8);
        if (row)
        {
          king_could_reach[index] |= king_could_reach[index - 8];
          if (col)
            king_could_reach[index] |= king_could_reach[index - 9];
          if (col < 7)
            king_could_reach[index] |= king_could_reach[index - 7];
        }
        if (row < 7)
        {
          king_could_reach[index] |= king_could_reach[index + 8];
          if (col)
            king_could_reach[index] |= king_could_reach[index + 7];
          if (col < 7)
            king_could_reach[index] |= king_could_reach[index + 9];
        }
        if (col)
          king_could_reach[index] |= king_could_reach[index - 1];
        if (col < 7)
          king_could_reach[index] |= king_could_reach[index + 1];

        if (king_could_reach[index] != orig_poss)
          found_another_move = true;
      }
  } while (found_another_move);

  // Promoted pieces could be anything.
  unsigned long long promoted_piece_could_reach[nr_squares_on_board + 1]; // = knight | bishop | rook | queen
  for (int index = a1; index <= h8; ++index)
    promoted_piece_could_reach[index] = (knight_could_reach[index] | bishop_could_reach[index] | rook_could_reach[index] | queen_could_reach[index]);

  pawn_could_reach[nr_squares_on_board] = 0;
  knight_could_reach[nr_squares_on_board] = 0;
  bishop_could_reach[nr_squares_on_board] = 0;
  rook_could_reach[nr_squares_on_board] = 0;
  queen_could_reach[nr_squares_on_board] = 0;
  king_could_reach[nr_squares_on_board] = 0;
  promoted_piece_could_reach[nr_squares_on_board] = 0;

  // Could pieces have reached their final squares?
  for (int index = a1; index <= h8; ++index)
    if (final[index].color == Black)
    {
      int const orig_square = cur_square_of_piece[final[index].orig_square];
      int const orig_piece = initial[final[index].orig_square].piece;
      switch (final[index].piece)
      {
        case Pawn:
          if (!((pawn_could_reach[orig_square] >> index) & 1U))
            return false;
          break;
        case Knight:
          if (orig_piece == Knight)
          {
            if (!((knight_could_reach[orig_square] >> index) & 1U))
              return false;
          }
          else
          {
            for (int promote = a1; promote <= h1; ++promote)
              if ((pawn_could_reach[orig_square] >> promote) & 1U)
                if ((knight_could_reach[promote] >> index) & 1U)
                  goto FOUND_KNIGHT_PROMOTION;
            return false;
FOUND_KNIGHT_PROMOTION:;
          }
          break;
        case Bishop:
          if (orig_piece == Bishop)
          {
            if (!((bishop_could_reach[orig_square] >> index) & 1U))
              return false;
          }
          else
          {
            for (int promote = a1; promote <= h1; ++promote)
              if ((pawn_could_reach[orig_square] >> promote) & 1U)
                if ((bishop_could_reach[promote] >> index) & 1U)
                  goto FOUND_BISHOP_PROMOTION;
            return false;
FOUND_BISHOP_PROMOTION:;
          }
          break;
        case Rook:
          if (orig_piece == Rook)
          {
            if (!((rook_could_reach[orig_square] >> index) & 1U))
              return false;
          }
          else
          {
            for (int promote = a1; promote <= h1; ++promote)
              if ((pawn_could_reach[orig_square] >> promote) & 1U)
                if ((rook_could_reach[promote] >> index) & 1U)
                  goto FOUND_ROOK_PROMOTION;
            return false;
FOUND_ROOK_PROMOTION:;
          }
          break;
        case Queen:
          if (orig_piece == Queen)
          {
            if (!((queen_could_reach[orig_square] >> index) & 1U))
              return false;
          }
          else
          {
            for (int promote = a1; promote <= h1; ++promote)
              if ((pawn_could_reach[orig_square] >> promote) & 1U)
                if ((queen_could_reach[promote] >> index) & 1U)
                  goto FOUND_QUEEN_PROMOTION;
            return false;
FOUND_QUEEN_PROMOTION:;
          }
          break;
        case King:
          if (!((king_could_reach[orig_square] >> index) & 1U))
            return false;
          break;
        case nr_piece_walks:
          if (!((pawn_could_reach[orig_square] >> index) & 1U))
          {
            for (int promote = a1; promote <= h1; ++promote)
              if ((pawn_could_reach[orig_square] >> promote) & 1U)
                if ((promoted_piece_could_reach[promote] >> index) & 1U)
                  goto FOUND_GENERIC_PROMOTION;
            return false;
FOUND_GENERIC_PROMOTION:;
          }
          break;
        case Dummy:
          if (orig_square != index)
            return false;
          break;
        default:
          assert(0);
          return false;
      }
    }

  return true;
}

void solve_target_position(slice_index si)
{
#if (defined(_WIN32) && !defined(_MSC_VER))|| defined(__CYGWIN__)
  /* Windows executables generated with gcc (both cross-compiling from Linux and
   * using cygwin) appear to have an optimiser error which may cause the value
   * of the expression save_king_square[Black] (but not the underlying memory!!)
   * to be modified from here to the end of the function (where
   * the value of being_solved.king_square[Black] is to be restored).
   *
   * This error doesn't manifest itself if save_king_square is volatile.
   *
   * Cf. bug report 3489394, which gives this problem as an example:
   * AnfangProblem
   * Steine Weiss  kh1 lh3 bh2
   * Steine Schwarz  ka2 dh8 ta1h6 la5f1 sg7a8 bc2e2f2b3c3a4h4h5
   * Forderung H=8
   * Option Intelligent
   * EndeProblem
   */
  volatile
#endif
  square const save_king_square[nr_sides] = { being_solved.king_square[White],
                                              being_solved.king_square[Black] };

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  {
    PieceIdType id;
    for (id = 0; id<=MaxPieceId; ++id)
      target_position[id].diagram_square = initsquare;
  }

  {
    square const *bnp;
    for (bnp = boardnum; *bnp!=initsquare; bnp++)
    {
      piece_walk_type const type = get_walk_of_piece_on_square(*bnp);
      if (type!=Empty && type!=Invalid)
      {
        Flags const flags = being_solved.spec[*bnp];
        PieceIdType const id = GetPieceId(flags);
        target_position[id].type = type;
        target_position[id].flags = flags;
        target_position[id].diagram_square = *bnp;
#if defined(DETAILS)
        target_position[id].usage = find_piece_usage(id);
#endif
      }
    }
  }

  /* solve the problem */
  ResetPosition(&initial_position);

  if (get_target_before_white_move(&initial_position) && target_position_is_ser_h_feasible(true)) {

#if defined(DETAILS)
    TraceText("target position:\n");
    trace_target_position(target_position,CapturesLeft[1]);
#endif

    pipe_solve_delegate(si);

    if (solve_result<=MOVE_HAS_SOLVED_LENGTH())
      solutions_found = true;

  }

  /* reset the old mating position */
  {
    square const *bnp;
    for (bnp = boardnum; *bnp!=initsquare; bnp++)
      if (!is_square_blocked(*bnp))
        empty_square(*bnp);
  }

  {
    PieceIdType id;
    for (id = 0; id<=MaxPieceId; ++id)
      if (target_position[id].diagram_square != initsquare)
        occupy_square(target_position[id].diagram_square,
                      target_position[id].type,
                      target_position[id].flags);
  }

  {
    piece_walk_type p;

    being_solved.number_of_pieces[White][King] = 1;
    being_solved.number_of_pieces[Black][King] = 1;

    for (p = King+1; p<=Bishop; ++p)
    {
      being_solved.number_of_pieces[White][p] = 2;
      being_solved.number_of_pieces[Black][p] = 2;
    }
  }

  being_solved.king_square[White] = save_king_square[White];
  being_solved.king_square[Black] = save_king_square[Black];

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void GenerateBlackKing(slice_index si)
{
  Flags const king_flags = black[index_of_king].flags;
  square const *bnp;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  assert(black[index_of_king].type==King);

  intelligent_init_reservations(MovesLeft[White],MovesLeft[Black],
                                MaxPiece[White],MaxPiece[Black]-1);

  for (bnp = boardnum; *bnp!=initsquare; ++bnp)
    if (is_square_empty(*bnp) /* *bnp isn't a hole*/
        && intelligent_reserve_black_king_moves_from_to(black[index_of_king].diagram_square,
                                                        *bnp))
    {

      {
        square s;
        for (s = 0; s!=maxsquare+4; ++s)
        {
          if (nr_reasons_for_staying_empty[s]>0)
            WriteSquare(&output_plaintext_engine,stdout,s);
          assert(nr_reasons_for_staying_empty[s]==0);
        }
      }

      occupy_square(*bnp,King,king_flags);
      being_solved.king_square[Black] = *bnp;
      black[index_of_king].usage = piece_is_king;

      init_guard_dirs(*bnp);

      if (goal_to_be_reached==goal_mate)
      {
        intelligent_mate_generate_checking_moves(si);
        intelligent_mate_generate_doublechecking_moves(si);
      }
      else
        pipe_solve_delegate(si);

      empty_square(*bnp);

      intelligent_unreserve();
    }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void IntelligentRegulargoal_types(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  if (being_solved.king_square[Black]!=initsquare)
  {
    testcastling = (   TSTCASTLINGFLAGMASK(White,q_castling)==q_castling
                    || TSTCASTLINGFLAGMASK(White,k_castling)==k_castling
                    || TSTCASTLINGFLAGMASK(Black,q_castling)==q_castling
                    || TSTCASTLINGFLAGMASK(Black,k_castling)==k_castling);

    assert(where_to_start_placing_black_pieces==boardnum);

    MaxPiece[Black] = 0;
    MaxPiece[White] = 0;

    black[index_of_king].type= get_walk_of_piece_on_square(being_solved.king_square[Black]);
    black[index_of_king].flags= being_solved.spec[being_solved.king_square[Black]];
    black[index_of_king].diagram_square= being_solved.king_square[Black];
    PieceId2index[GetPieceId(being_solved.spec[being_solved.king_square[Black]])] = index_of_king;
    ++MaxPiece[Black];

    if (being_solved.king_square[White]==initsquare)
      white[index_of_king].usage = piece_is_missing;
    else
    {
      white[index_of_king].usage = piece_is_unused;
      white[index_of_king].type = get_walk_of_piece_on_square(being_solved.king_square[White]);
      white[index_of_king].flags = being_solved.spec[being_solved.king_square[White]];
      white[index_of_king].diagram_square = being_solved.king_square[White];
      PieceId2index[GetPieceId(being_solved.spec[being_solved.king_square[White]])] = index_of_king;
      assert(white[index_of_king].type==King);
    }

    ++MaxPiece[White];

    {
      square const *bnp;

      nextply(White);

      for (bnp = boardnum; *bnp!=initsquare; ++bnp)
        if (being_solved.king_square[White]!=*bnp && TSTFLAG(being_solved.spec[*bnp],White))
        {
          white[MaxPiece[White]].type = get_walk_of_piece_on_square(*bnp);
          white[MaxPiece[White]].flags = being_solved.spec[*bnp];
          white[MaxPiece[White]].diagram_square = *bnp;
          white[MaxPiece[White]].usage = piece_is_unused;
          if (get_walk_of_piece_on_square(*bnp)==Pawn)
            moves_to_white_prom[MaxPiece[White]] = intelligent_count_moves_to_white_promotion(*bnp);
          PieceId2index[GetPieceId(being_solved.spec[*bnp])] = MaxPiece[White];
          ++MaxPiece[White];
        }

      for (bnp = boardnum; *bnp!=initsquare; ++bnp)
        if (being_solved.king_square[Black]!=*bnp && TSTFLAG(being_solved.spec[*bnp],Black))
        {
          black[MaxPiece[Black]].type = get_walk_of_piece_on_square(*bnp);
          black[MaxPiece[Black]].flags = being_solved.spec[*bnp];
          black[MaxPiece[Black]].diagram_square = *bnp;
          black[MaxPiece[Black]].usage = piece_is_unused;
          PieceId2index[GetPieceId(being_solved.spec[*bnp])] = MaxPiece[Black];
          ++MaxPiece[Black];
        }

      finply();
    }

    StorePosition(&initial_position);

    /* clear board */
    {
      square const *bnp;
      for (bnp= boardnum; *bnp!=initsquare; ++bnp)
        if (!is_square_blocked(*bnp))
          empty_square(*bnp);
    }

    {
      piece_walk_type p;
      for (p = King; p<=Bishop; ++p)
      {
        being_solved.number_of_pieces[White][p] = 2;
        being_solved.number_of_pieces[Black][p] = 2;
      }
    }

    /* generate final positions */
    GenerateBlackKing(si);

    ResetPosition(&initial_position);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void goal_to_be_reached_goal(slice_index si,
                                    stip_structure_traversal *st)
{
  goal_type * const goal = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  assert(*goal==no_goal);
  *goal = SLICE_U(si).goal_handler.goal.type;

  stip_traverse_structure_children(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Initialise the variable holding the goal to be reached
 */
static goal_type determine_goal_to_be_reached(slice_index si)
{
  stip_structure_traversal st;
  goal_type result = no_goal;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  stip_structure_traversal_init(&st,&result);
  stip_structure_traversal_override_single(&st,
                                           STGoalReachedTester,
                                           &goal_to_be_reached_goal);
  stip_structure_traversal_override_single(&st,
                                           STTemporaryHackFork,
                                           &stip_traverse_structure_children_pipe);
  stip_traverse_structure(si,&st);

  TraceValue("%u",goal_to_be_reached);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Initialise a STGoalReachableGuardFilter slice
 * @return identifier of allocated slice
 */
static slice_index alloc_goalreachable_guard_filter(goal_type goal)
{
  slice_index result;
  slice_type type;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",goal);
  TraceFunctionParamListEnd();

  switch (goal)
  {
    case goal_mate:
      type = STGoalReachableGuardFilterMate;
      break;

    case goal_stale:
      type = STGoalReachableGuardFilterStalemate;
      break;

    case goal_proofgame:
    case goal_atob:
      type = proof_make_goal_reachable_type();
      break;

    default:
      assert(0);
      type = no_slice_type;
      break;
  }

  if (type!=no_slice_type)
    result = alloc_pipe(type);
  else
    result = no_slice;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

static
void goalreachable_guards_inserter_help_move(slice_index si,
                                             stip_structure_traversal *st)
{
  goal_type const * const goal = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  {
    slice_index const prototype = alloc_goalreachable_guard_filter(*goal);
    if (prototype!=no_slice)
      help_branch_insert_slices(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static
void
goalreachable_guards_duplicate_avoider_inserter(slice_index si,
                                                stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children(si,st);

  if (SLICE_U(si).goal_handler.goal.type==goal_mate
      || SLICE_U(si).goal_handler.goal.type==goal_stale)
  {
    slice_index const prototypes[] = {
        alloc_pipe(STIntelligentDuplicateAvoider),
        alloc_pipe(STIntelligentSolutionRememberer)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    help_branch_insert_slices(si,prototypes,nr_prototypes);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor goalreachable_guards_inserters[] =
{
  { STReadyForHelpMove,  &goalreachable_guards_inserter_help_move         },
  { STGoalReachedTester, &goalreachable_guards_duplicate_avoider_inserter },
  { STTemporaryHackFork, &stip_traverse_structure_children_pipe           }
};

enum
{
  nr_goalreachable_guards_inserters = (sizeof goalreachable_guards_inserters
                                       / sizeof goalreachable_guards_inserters[0])
};

/* Instrument stipulation with STgoal_typereachableGuard slices
 * @param si identifies slice where to start
 */
static void insert_goalreachable_guards(slice_index si, goal_type goal)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",goal);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  assert(goal!=no_goal);

  stip_structure_traversal_init(&st,&goal);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_conditional_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override(&st,
                                    goalreachable_guards_inserters,
                                    nr_goalreachable_guards_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static slice_index find_goal_tester_fork(slice_index si)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  {
    slice_index const branch_goal_fork = branch_find_slice(STEndOfBranchGoalImmobile,
                                                           si,
                                                           stip_traversal_context_intro);
    if (branch_goal_fork==no_slice)
    {
      slice_index const branch_goal = branch_find_slice(STEndOfBranch,
                                                        si,
                                                        stip_traversal_context_intro);
      assert(branch_goal!=no_slice);
      result = find_goal_tester_fork(SLICE_NEXT2(branch_goal));
    }
    else
      result = branch_find_slice(STGoalReachedTester,
                                 SLICE_NEXT2(branch_goal_fork),
                                 stip_traversal_context_intro);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

typedef struct
{
    goal_type goal;
    slice_index is_maxtime_active;
    slice_index is_maxsolutions_active;
} insertion_struct_type;

static void remember_maxtime(slice_index si, stip_structure_traversal *st)
{
  insertion_struct_type * const insertion = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  insertion->is_maxtime_active = si;

  stip_traverse_structure_children(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void remember_maxsolutions(slice_index si, stip_structure_traversal *st)
{
  insertion_struct_type * const insertion = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  insertion->is_maxsolutions_active = si;

  stip_traverse_structure_children(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_maxtime(slice_index si, slice_index incomplete)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",incomplete);
  TraceFunctionParamListEnd();

  assert(SLICE_TYPE(incomplete)==STPhaseSolvingIncomplete);

  {
    slice_index const prototypes[] = {
        alloc_maxtime_guard(incomplete),
        alloc_maxtime_guard(incomplete),
        alloc_maxtime_guard(incomplete)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    slice_insertion_insert(si,prototypes,nr_prototypes);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_maxsolutions(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  {
    slice_index const prototypes[] = {
        alloc_maxsolutions_guard_slice(),
        alloc_maxsolutions_guard_slice(),
        alloc_maxsolutions_guard_slice()
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    slice_insertion_insert(si,prototypes,nr_prototypes);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void intelligent_filter_inserter(slice_index si,
                                        stip_structure_traversal *st)
{
  insertion_struct_type const * const insertion = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  switch (insertion->goal)
  {
    case goal_proofgame:
    case goal_atob:
    {
      slice_index const prototype = alloc_intelligent_proof();
      slice_insertion_insert(si,&prototype,1);
      break;
    }

    case goal_mate:
    case goal_stale:
    {
      slice_index const prototypes[] = {
          alloc_pipe(STIntelligentFilter),
          alloc_pipe(STIntelligentFlightsGuarder),
          alloc_pipe(STIntelligentFlightsBlocker),
          insertion->goal==goal_mate
          ? alloc_intelligent_mate_target_position_tester(find_goal_tester_fork(si))
          : alloc_intelligent_stalemate_target_position_tester(),
          alloc_pipe(STIntelligentTargetPositionFound)
      };
      enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
      slice_insertion_insert(si,prototypes,nr_prototypes);

      if (insertion->is_maxtime_active!=no_slice)
        insert_maxtime(si,SLICE_NEXT2(insertion->is_maxtime_active));
      if (insertion->is_maxsolutions_active!=no_slice)
        insert_maxsolutions(si);
      break;
    }

    default:
      assert(0);
      break;
  }

  {
    slice_index const prototype = alloc_intelligent_moves_left_initialiser();
    slice_insertion_insert(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor intelligent_filters_inserters[] =
{
  { STMaxTimeSetter,           &remember_maxtime                      },
  { STMaxSolutionsInitialiser, &remember_maxsolutions                 },
  { STHelpAdapter,             &intelligent_filter_inserter           },
  { STTemporaryHackFork,       &stip_traverse_structure_children_pipe }
};

enum
{
  nr_intelligent_filters_inserters = (sizeof intelligent_filters_inserters
                                     / sizeof intelligent_filters_inserters[0])
};

/* Instrument stipulation with STgoal_typereachableGuard slices
 * @param si identifies slice where to start
 */
static void insert_intelligent_filters(slice_index si, goal_type goal)
{
  stip_structure_traversal st;
  insertion_struct_type insertion = { goal, no_slice, no_slice };

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",goal);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  stip_structure_traversal_init(&st,&insertion);
  stip_structure_traversal_override(&st,
                                    intelligent_filters_inserters,
                                    nr_intelligent_filters_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* How well does the stipulation support intelligent mode?
 */
typedef enum
{
  intelligent_not_supported,
  intelligent_not_active_by_default,
  intelligent_active_by_default
} support_for_intelligent_mode;

typedef struct
{
  support_for_intelligent_mode support;
  goal_type goal;
} detector_state_type;

static
void intelligent_mode_support_detector_or(slice_index si,
                                          stip_structure_traversal *st)
{
  detector_state_type * const state = st->param;
  support_for_intelligent_mode support1;
  support_for_intelligent_mode support2;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (state->support!=intelligent_not_supported)
  {
    /* enumerators are ordered so that the weakest support has the
     * lowest enumerator etc. */
    {
      enum
      {
        ensure_intelligent_not_supported_lt_intelligent_not_active_by_default = 1/(intelligent_not_supported<intelligent_not_active_by_default),
        ensure_intelligent_not_active_by_default_lt_intelligent_active_by_default = 1/(intelligent_not_active_by_default<intelligent_active_by_default)
      };
    }

    stip_traverse_structure_binary_operand1(si,st);
    support1 = state->support;

    stip_traverse_structure_binary_operand2(si,st);
    support2 = state->support;

    state->support = support1<support2 ? support1 : support2;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void intelligent_mode_support_none(slice_index si,
                                          stip_structure_traversal *st)
{
  detector_state_type * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  state->support = intelligent_not_supported;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void intelligent_mode_support_goal_tester(slice_index si,
                                                 stip_structure_traversal *st)
{
  detector_state_type * const state = st->param;
  goal_type const goal = SLICE_U(si).goal_handler.goal.type;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (state->goal==no_goal)
  {
    switch (goal)
    {
      case goal_mate:
      case goal_stale:
        if (state->support!=intelligent_not_supported)
          state->support = intelligent_not_active_by_default;
        break;

      case goal_proofgame:
      case goal_atob:
        if (state->support!=intelligent_not_supported)
          state->support = intelligent_active_by_default;
        break;

      default:
        state->support = intelligent_not_supported;
        break;
    }

    state->goal = goal;
  }
  else if (state->goal!=goal)
    state->support = intelligent_not_supported;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor intelligent_mode_support_detectors[] =
{
  { STAnd,               &intelligent_mode_support_none         },
  { STOr,                &intelligent_mode_support_detector_or  },
  { STNot,               &intelligent_mode_support_none         },
  { STConstraintSolver,  &intelligent_mode_support_none         },
  { STConstraintTester,  &intelligent_mode_support_none         },
  { STReadyForDefense,   &intelligent_mode_support_none         },
  { STGoalReachedTester, &intelligent_mode_support_goal_tester  },
  { STTemporaryHackFork, &stip_traverse_structure_children_pipe }
};

enum
{
  nr_intelligent_mode_support_detectors
  = (sizeof intelligent_mode_support_detectors
     / sizeof intelligent_mode_support_detectors[0])
};

/* Determine whether the stipulation supports intelligent mode, and
 * how much so
 * @param si identifies slice where to start
 * @return degree of support for ingelligent mode by the stipulation
 */
static support_for_intelligent_mode stip_supports_intelligent(slice_index si)
{
  detector_state_type state = { intelligent_not_active_by_default, no_goal };
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,&state);
  stip_structure_traversal_override(&st,
                                    intelligent_mode_support_detectors,
                                    nr_intelligent_mode_support_detectors);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",state.support);
  TraceFunctionResultEnd();
  return state.support;
}

/* Initialize intelligent mode if the user or the stipulation asks for
 * it
 * @param si identifies slice where to start
 * @return false iff the user asks for intelligent mode, but the
 *         stipulation doesn't support it
 */
boolean init_intelligent_mode(slice_index si)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  goal_to_be_reached = no_goal;

  switch (stip_supports_intelligent(si))
  {
    case intelligent_not_supported:
      result = !OptFlag[intelligent];
      break;

    case intelligent_not_active_by_default:
      result = true;
      if (OptFlag[intelligent])
      {
        goal_to_be_reached = determine_goal_to_be_reached(si);
        insert_intelligent_filters(si,goal_to_be_reached);
        insert_goalreachable_guards(si,goal_to_be_reached);
        check_no_king_is_possible();
      }
      break;

    case intelligent_active_by_default:
      result = true;
      goal_to_be_reached = determine_goal_to_be_reached(si);
      insert_intelligent_filters(si,goal_to_be_reached);
      insert_goalreachable_guards(si,goal_to_be_reached);
      check_no_king_is_possible();
      break;

    default:
      assert(0);
      result = false;
      break;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}
