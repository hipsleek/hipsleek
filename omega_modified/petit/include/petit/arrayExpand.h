/* $Id: arrayExpand.h,v 1.1 2010-12-10 07:42:08 locle Exp $ */
/******************************************************
 *                                                    *
 * Array expansion and privatization.                 *
 * Written by Vadim Maslov vadik@cs.umd.edu 10/26/92. *
 *                                                    *
 ******************************************************/

#ifndef Already_Included_Array_Expand
#define Already_Included_Array_Expand

#include <petit/tree.h>

namespace omega {

int  ArrayExpansion(int);
int  ZapExpand(ddnode *);
int  Privatization(int);

}

#endif
