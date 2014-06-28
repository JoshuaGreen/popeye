#include "output/plaintext/protocol.h"
#include "output/plaintext/stdio.h"

#include <stdarg.h>
#include <stdio.h>

static FILE *TraceFile;
static char const *open_mode = "a";

/* Remember for this run's proptocol (if any) to overwrite (rather than append
 * to) a previous run's protocol (if any)
 */
void protocol_overwrite(void)
{
  open_mode = "w";
}

/* Open a new protocol file
 * @param filename name of protocol file
 * @return the opened file (for writing some intro text)
 *         0 if it couln't be opened
 * @note the previous protocol file (if any) is closed
 */
FILE *protocol_open(char const *filename)
{
  if (TraceFile!=NULL)
    fclose(TraceFile);

  TraceFile = fopen(filename,open_mode);

  return TraceFile;
}

/* like putchar().
 * If a trace file is active, output goes to the trace file as well
 * @return the result of writing to *regular
 */
int protocol_fputc(int c, FILE *regular)
{
  int const result = fputc(c,regular);

  if (TraceFile!=0)
    fputc(c,TraceFile);

  return result;
}

/* like vprintf().
 * If a trace file is active, output goes to the trace file as well
 * @return the result of writing to *regular
 */
int protocol_vfprintf(FILE *regular, char const *format, va_list args)
{
  int result;

  if (TraceFile==0)
    result = vfprintf(regular,format,args);
  else
  {
    va_list args2;
    va_copy(args2,args);
    result = vfprintf(regular,format,args);
    vfprintf(TraceFile,format,args2);
    va_end(args2);
  }

  return result;
}

/* like printf().
 * If a trace file is active, output goes to the trace file as well
 * @return the result of writing to *regular
 */
int protocol_fprintf(FILE *regular, char const *format, ...)
{
  int result;

  va_list args;
  va_start(args,format);
  result = protocol_vfprintf(regular,format,args);
  va_end(args);

  return result;
}

/* like fprintf_r().
 * If a trace file is active, output goes to the trace file as well
 * @return the result of writing to *regular
 */
int protocol_fprintf_r(FILE *regular, int width, char const *format, ...)
{
  int result;
  va_list args;

  va_start(args,format);

  if (TraceFile==0)
    result = vfprintf_r(regular,width,format,args);
  else
  {
    va_list args2;

    va_copy(args2,args);
    result = vfprintf_r(regular,width,format,args);
    vfprintf_r(TraceFile,width,format,args2);
    va_end(args2);
  }

  va_end(args);

  return result;
}

/* like fprintf_c().
 * If a trace file is active, output goes to the trace file as well
 * @return the result of writing to *regular
 */
int protocol_fprintf_c(FILE *regular, int width, char const *format, ...)
{
  int result;
  va_list args;

  va_start(args,format);

  if (TraceFile==0)
    result = vfprintf_c(regular,width,format,args);
  else
  {
    va_list args2;

    va_copy(args2,args);
    result = vfprintf_c(regular,width,format,args);
    vfprintf_c(TraceFile,width,format,args2);
    va_end(args2);
  }

  va_end(args);

  return result;
}

/* like fputs_c_multi().
 * If a trace file is active, output goes to the trace file as well
 */
void protocol_fputs_c_multi(FILE *regular, int width, char const *lines)
{
  fputs_c_multi(regular,width,lines);

  if (TraceFile!=0)
    fputs_c_multi(TraceFile,width,lines);
}

/* like fflush().
 * If a trace file is active, output goes to the trace file as well
 * @return the result of writing to *regular
 */
int protocol_fflush(FILE *regular)
{
  if (TraceFile!=0)
    fflush(TraceFile);

  return fflush(regular);
}
