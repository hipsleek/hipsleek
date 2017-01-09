/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Simple example for non-termination
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
	while (x >= 0) {
		x++;
	}
}

