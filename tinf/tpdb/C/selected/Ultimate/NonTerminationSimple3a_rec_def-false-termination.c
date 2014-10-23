/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for c >= 0.
 */

extern int __VERIFIER_nondet_int();

int __VERIFIER_nondet_nat()
{
  int x = __VERIFIER_nondet_int();
  if (x < 0) return -x;
  else return x;
}

void loop(int x, int c)
{
  if (x >= 0) {
    x += c;
    loop(x, c);
  }
}

int main()
{
	int c = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_nat();
	loop(x, c);
  loop(x, -c);
}

