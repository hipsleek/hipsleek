/* $Id: timer.h,v 1.1 2010-12-10 07:42:14 locle Exp $ */
#ifndef Already_Included_Timer
#define Already_Included_Timer

namespace omega {

void start_clock( void );
long clock_diff( void );  /* return user time since start_clock */

}

#endif

