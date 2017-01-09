/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
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
	int c = 0;
	
	if (c != 0) {
		return 1;
	}
  while (x >= 0) {
    x += c;
  }
	return 0;
}

