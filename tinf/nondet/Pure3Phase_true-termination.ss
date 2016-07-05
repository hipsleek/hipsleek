/*
 * Date: 2014-06-29
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following 3-phase ranking function:
 * f_0(x, y, z) = z
 * f_1(x, y, z) = y
 * f_2(x, y, z) = x
 *
 * The program does not have a nested ranking function.
 */

void f (int x, int y, int z, int c)
{
  if (x >= 0) {
    c = __VERIFIER_nondet_int();
    if (c > 0) {
      f(x + y, y + z, z - 1, c);
    } else {
      f(x + z, y + z, z - 1, c);
    }
  }
}


void g (int x, int y, int z)
{
  if (x >= 0) {
    //int c = __VERIFIER_nondet_int();
    if (__VERIFIER_nondet_int() > 0) {
      g(x + y, y + z, z - 1);
    } else {
      g(x + z, y + z, z - 1);
    }
  }
}
