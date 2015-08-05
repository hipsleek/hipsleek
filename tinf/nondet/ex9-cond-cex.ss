/*
 * Program from Fig.1 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

void loop(int x, int y, int z, int d)
{
  if (x > 0 && y > 0) {
    if (__VERIFIER_nondet_int() > 0) {
      x = x - d;
      y = __VERIFIER_nondet_int();
      z = z - 1;
    } else {
      y = y - d;
    }
    loop(x, y, z, d);
  }
}
