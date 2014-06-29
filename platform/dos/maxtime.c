#include "platform/maxtime_impl.h"
#include "utilities/boolean.h"
#include <limits.h>

boolean setMaxtimeTimer(maxtime_type seconds)
{
  if (seconds==no_time_set)
  {
    periods_counter = 0;
    nr_periods = 1;
    return true;
  }
  else
  {
    periods_counter = 1;
    nr_periods = 0;
    return false;
  }
}

void resetMaxtimeTimer(void)
{
}

void platform_init(void)
{
}
