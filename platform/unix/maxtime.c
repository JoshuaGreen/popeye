#include "../maxtime.h"
#include "../../boolean.h"
#include "../../pymsg.h"
#include <stdio.h>
#include <stdlib.h>

#if defined(SIGNALS)

#include <unistd.h>
#include "../../py.h"
#include "../../pydata.h"
#include "../../pyhash.h"

/* default signal handler: */
static void ReportSignalAndBailOut(int sig)
{
  sprintf(GlobalStr, GetMsgString(Abort), sig, MakeTimeString());
  StdString(GlobalStr);
  exit(1);
}

/* specific signal handlers: */
void sigUsr1Handler(int sig)
{
  IncHashRateLevel();
  signal(sig, &sigUsr1Handler);
}

void sigUsr2Handler(int sig)
{
  DecHashRateLevel();
  signal(sig, &sigUsr2Handler);
}

/* this initialisation is valid only for Unix.
 * I do not know whether there are other handling
 * possiblilities. May be on Mac's and Amigas.
 * or windows?
 */
static int const SignalToCatch[] =
{
  SIGHUP
  , SIGINT
  , SIGQUIT
  , SIGTERM
#if !defined(_hpux) && !defined(__GO32__)
  /* not supported by HP-UX */
  /* not supported by DJGPP */
  , SIGVTALRM
  , SIGXCPU
  , SIGXFSZ
#endif /* HPUX, __GO32__ */
};

enum
{
  nrSignals = sizeof SignalToCatch / sizeof SignalToCatch[0]
};

static void ReDrawBoard(int sig)
{
  /* I did this, to see more accurately what position popeye is
     working on.  ElB
  */
  /* If a position can be reached by 1000's of move sequences than the
     position is of almost no value. The history is more important.
     TLi
  */
  ply pl;

  WritePosition();

  /* and write (some information about) the sequences of moves that
     lead to this position.
  */
  for (pl= 3; pl < nbply; pl++)
  {
    WritePiece(pjoue[pl-1]);
    WriteSquare(move_generation_stack[repere[pl]].departure);
    StdChar('-');
    WriteSquare(move_generation_stack[repere[pl]].arrival);
    if (norm_prom[pl-1]) {
      StdChar('=');
      WritePiece(norm_prom[pl-1]);
    }
    StdString("   ");
  }
  StdChar('\n');

  signal(sig,&ReDrawBoard);
}

static void solvingTimeOver(int sig)
{
  /* To stop the calculation of a problem after a given amount of time
   * is over.
   */
  maxtime_status = MAXTIME_TIMEOUT;
  
  signal(sig,&solvingTimeOver);
}

void initMaxtime(void)
{
  /* register default handler for all supported signals */
  int i;
  for (i=0; i<nrSignals; ++i)
    signal(SignalToCatch[i],&ReportSignalAndBailOut);

  /* override default handler with specific handlers.
   * this code would be much more robust, if some information about
   * the signals were available without knowing the semantics of the
   * Unix-Signal numbers.
   * At least the maximum signal-number should be defined and for what
   * signals the handling can be redefined
   */
#if defined(HASHRATE)
  signal(SIGUSR1, &sigUsr1Handler);
  signal(SIGUSR2, &sigUsr2Handler);
#endif /*HASHRATE*/
  signal(SIGALRM, &solvingTimeOver);
  signal(SIGHUP,  &ReDrawBoard);
}

void setMaxtime(unsigned int *seconds)
{
  if (*seconds==UINT_MAX)
    maxtime_status = MAXTIME_IDLE;
  else
  {
    maxtime_status = MAXTIME_TIMING;
    alarm(*seconds);
  }
}

#else

void initMaxtime(void)
{
  /* no initialization necessary */
}

void setMaxtime(unsigned int *seconds)
{
  VerifieMsg(NoMaxTime);
  FlagTimeOut = true;
}

#endif /*SIGNALS*/
