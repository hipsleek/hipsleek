/*
 * Program from Fig.2 of
 * 2013WST - Urban - Piecewise-Defined Ranking Functions
 *
 * Date: 12.12.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */


void loop (int x) {
  if (x <= 10) {
    if (x > 6) {
      loop(x + 2);
    } else loop(x);
  } else return;
}
