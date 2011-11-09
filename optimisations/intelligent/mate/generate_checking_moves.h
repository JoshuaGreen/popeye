#if !defined(OPTIMISATION_INTELLIGENT_MATE_GENERATE_CHECKING_MOVES_H)
#define OPTIMISATION_INTELLIGENT_MATE_GENERATE_CHECKING_MOVES_H

#include "py.h"

typedef struct
{
    int dir;       /* direction over which a rider captures or intercepts */
    square target; /* target square of the disturbance */
} disturbance_by_rider_elmt_type;

typedef disturbance_by_rider_elmt_type disturbance_by_rider_type[maxsquare+4];

/* disturbances by rider types */
disturbance_by_rider_type DisturbMateDirRider[4];

typedef struct
{
    unsigned int start; /* start and ... */
    unsigned int end;   /* ... end index into DisturbMateDirRider */
} disturbance_by_rider_index_range_type;

extern disturbance_by_rider_index_range_type disturbance_by_rider_index_ranges[Bishop-Queen+1];

/* disturbances by Knight */
extern int DisturbMateDirKnight[maxsquare+4];


typedef enum
{
  disturbance_by_pawn_none,
  disturbance_by_pawn_interception_single,
  disturbance_by_pawn_interception_double,
  disturbance_by_pawn_capture
} disturbance_by_pawn_type;

/* disturbances by Pawn */
extern disturbance_by_pawn_type DisturbMateDirPawn[maxsquare+4];


void intelligent_mate_generate_checking_moves(void);

#endif
