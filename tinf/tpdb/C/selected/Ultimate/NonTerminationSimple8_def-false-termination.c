/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 */

extern int __VERIFIER_nondet_int();

int __VERIFIER_nondet_pos()
{
  int x = __VERIFIER_nondet_int();
  if (x < 0) return -x;
  else return x + 1;
}

int main()
{
	int x = __VERIFIER_nondet_pos();
	while (x >= 0) {
		if (__VERIFIER_nondet_int()) {
			x += 1;
		} else if (__VERIFIER_nondet_int()) {
			x += 2;
		} else if (__VERIFIER_nondet_int()) {
			x += 3;
		} else if (__VERIFIER_nondet_pos()) {
			x += 4;
		} else {
			break;
		}
	}
	return 0;
}

