/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 */

global int c = 5;

int main()
{
	int x = __VERIFIER_nondet_int();
  //assume x >= 0;
  while (x >= 0) {
		x += c;
	}
	return 0;
}
