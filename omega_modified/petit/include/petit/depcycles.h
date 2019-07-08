/* $Id: depcycles.h,v 1.1 2010-12-10 07:42:10 locle Exp $ */
#ifndef Already_Included_Depcycles
#define Already_Included_Depcycles

#include <basic/bool.h>

namespace omega {

extern void FindFlowCycles(bool,bool);
extern void reset_flow_cycle_bits(bool);
extern void InvertDDdistances(void);

}

#endif
