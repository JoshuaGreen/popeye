#include "output/plaintext/pieces.h"
#include "output/plaintext/language_dependant.h"
#include "output/plaintext/message.h"
#include "output/plaintext/protocol.h"
#include "pieces/attributes/neutral/neutral.h"
#include "pieces/walks/classification.h"
#include "pieces/walks/hunters.h"

#include "debugging/assert.h"
#include <ctype.h>
#include <string.h>

boolean WriteSpec(output_engine_type const * engine, FILE *file,
                  Flags sp, piece_walk_type p, boolean printcolours)
{
  boolean ret = false;
  piece_flag_type spname;

  if (is_piece_neutral(sp))
  {
    (*engine->fputc)(tolower(ColourString[UserLanguage][colour_neutral][0]),file);
    ret = true;
  }
  else if (printcolours)
  {
    if (areColorsSwapped)
    {
      if (TSTFLAG(sp,White))
        (*engine->fputc)(tolower(ColourString[UserLanguage][colour_black][0]),file);
      if (TSTFLAG(sp,Black))
        (*engine->fputc)(tolower(ColourString[UserLanguage][colour_white][0]),file);
    }
    else
    {
      if (TSTFLAG(sp,White))
        (*engine->fputc)(tolower(ColourString[UserLanguage][colour_white][0]),file);
      if (TSTFLAG(sp,Black))
        (*engine->fputc)(tolower(ColourString[UserLanguage][colour_black][0]),file);
    }
  }

  for (spname = nr_sides; spname<nr_piece_flags; ++spname)
    if ((spname!=Volage || !CondFlag[volage])
        && (spname!=Patrol || !CondFlag[patrouille])
        && (spname!=Beamtet || !CondFlag[beamten])
        && (spname!=Royal || !is_king(p))
        && TSTFLAG(sp, spname))
    {
      (*engine->fputc)(tolower(PieSpString[UserLanguage][spname-nr_sides][0]),file);
      ret = true;
    }

  return ret;
}

void WriteWalk(output_engine_type const * engine, FILE *file, piece_walk_type p)
{
  if (p<Hunter0 || p>= (Hunter0 + max_nr_hunter_walks))
  {
    char const p1 = PieceTab[p][1];
    (*engine->fputc)(toupper(PieceTab[p][0]),file);
    if (p1!=' ')
      (*engine->fputc)(toupper(p1),file);
  }
  else
  {
    unsigned int const i = p-Hunter0;
    WriteWalk(engine,file,huntertypes[i].away);
    (*engine->fputc)('/',file);
    WriteWalk(engine,file,huntertypes[i].home);
  }
}

void WriteSquare(output_engine_type const * engine, FILE *file, square i)
{
  (*engine->fputc)('a' - nr_files_on_board + i%onerow,file);
  if (isBoardReflected)
    (*engine->fputc)('8' + nr_rows_on_board - i/onerow,file);
  else
    (*engine->fputc)('1' - nr_rows_on_board + i/onerow,file);
}

void AppendSquare(char *List, square s)
{
  char    add[4];

  add[0]= ' ';
  add[1]= 'a' - nr_files_on_board + s%onerow;
  add[2]= '1' - nr_rows_on_board + s/onerow;
  add[3]= '\0';
  strcat(List, add);
}
