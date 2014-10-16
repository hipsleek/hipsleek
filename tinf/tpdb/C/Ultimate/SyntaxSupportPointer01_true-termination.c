/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
#include "stdhip2.h"

extern int __VERIFIER_nondet_int(void);

int main() {
	int *p = malloc(sizeof(int));
	while (*p >= 0) 
  /*@
    requires p::int*<q,_,_>
    ensures true;
   */
	{
		(*p)--;
	}
	return 0;
}
