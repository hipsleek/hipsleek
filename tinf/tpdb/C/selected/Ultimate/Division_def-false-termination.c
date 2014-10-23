/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for 0 <= x <= 10
 * due to rounding in integer division.
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
	int y = __VERIFIER_nondet_nat() % 10 + 1;
	while (y >= 0 && y <= 10) {
		y = (2*y + 1) / 2;
	}
	return 0;
}
