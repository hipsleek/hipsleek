/* $Id: definitions.h,v 1.1 2010-12-10 07:42:10 locle Exp $ */
#ifndef Already_Included_Definitions
#define Already_Included_Definitions

#include <basic/bool.h>

namespace omega {

#define set(v)      (v) = true
#define reset(v)    (v) = false

#define Assert(c,t)     {if (!(c)) ErrAssert(t);}
#define UserAssert(c,t) {if (!(c)) Error(t);}
}

#endif
