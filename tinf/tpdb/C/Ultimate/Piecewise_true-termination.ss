/*
 * Date: 08.10.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * An example tailored to the piecewise ranking template.
 *
 * A ranking function is
 *
 * f(p, q) = min(p, q).
 *
 */

void loop (int p, int q)
  /*
  case {
    p > 0 & q > 0 -> case {
      q < p -> requires Term[q] ensures true;
      q >= p -> requires Term[p] ensures true;
    }
    !(p > 0 & q > 0) -> requires Term ensures true;
  }
  */
  infer [@term]
  //requires true
  //ensures true;
  
  case {
    ((p<=0 & 1<=q) | q<=0) -> requires Term ensures true; // Problem (FIXED)
    1<=q & q<p -> requires true ensures true; 
    1<=p & p<=q -> requires true ensures true; 
  }
  
  /*
  case {
    p > 0 & q > 0 -> case {
      q < p -> requires true ensures true;
      q >= p -> requires true ensures true;
    }
    !(p > 0 & q > 0) -> requires true ensures true;
  }
  */
{
  if (q > 0 && p > 0) {
    if (q < p) {
      q = q - 1;
      p = __VERIFIER_nondet_int();
    } else {
      p = p - 1;
      q = __VERIFIER_nondet_int();
    }
    loop(p, q);
  }
}
