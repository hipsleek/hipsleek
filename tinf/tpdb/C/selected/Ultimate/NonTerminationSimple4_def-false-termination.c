/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for y >= 5 & x >= 0.
 */

extern int __VERIFIER_nondet_int();

int __VERIFIER_nondet_nat()
{
  int x = __VERIFIER_nondet_int();
  if (x < 0) return -x;
  else return x;
}

int main()
{
	int x = __VERIFIER_nondet_nat();
	int y = __VERIFIER_nondet_nat() + 5;
	if (y < 5) {
		return 0;
	}
	while (x >= 0) {
		y -= 1;
	}
	return 0;
}

