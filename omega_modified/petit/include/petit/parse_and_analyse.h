/* $Id: parse_and_analyse.h,v 1.1 2010-12-10 07:42:12 locle Exp $ */
#ifndef Already_Included_Calc_Depends
#define Already_Included_Calc_Depends

namespace omega {

extern int parse_and_analyse(char *filename);

extern int re_analyse(int print);

extern void write_depends(int found, char *fname);

extern void compare_tests(int found);

extern void calculate_depnum();

extern int do_reopen(int dummy);

extern int do_newfile(int dummy);

}

#endif
