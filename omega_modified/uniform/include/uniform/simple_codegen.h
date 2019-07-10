/* $Id: simple_codegen.h,v 1.1 2010-12-10 07:42:37 locle Exp $ */
#ifndef Already_Included_Simple_CodeGen
#define Already_Included_Simple_CodeGen

namespace omega {

extern Tuple<int> barrier_required[max_nest][max_stmts];
extern Tuple<int> post_required[max_nest][max_stmts];
extern Tuple<int> wait_required[max_nest][max_stmts];
extern Tuple<int> post_wait_rev[max_nest][max_stmts];

extern int parallel_reduction[max_stmts];

extern void simple_codegen();

}

#endif
