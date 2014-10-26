/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(p, q, *q) = (q, *q)
 *
 */
#include "stdhip.h"

extern int __VERIFIER_nondet_int(void);

int main() {
	int *p = malloc(1048 * sizeof(int));
	int *q = p; // Error: Do not satisfy the precondition of while
  while (*q >= 0 && q < p + 1048) 
  /*@
    requires p::int*<_, op> * q::int*<vq, oq>
    ensures true;
   */
	{
		if (__VERIFIER_nondet_int()) {
			q++;
		} else {
			(*q)--;
		}
	}
	return 0;
}
