/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int();

int __VERIFIER_nondet_nat()
{
  int x = __VERIFIER_nondet_int();
  if (x < 0) return -x;
  else return x;
}

int main() {
	int x = __VERIFIER_nondet_nat() + 2;
	while (x > 1) {
		x = 2*x;
	}
	return 0;
}
