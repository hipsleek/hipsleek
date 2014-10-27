int test_fun(int x, int y, int z)
{
  if(y <= 0) {
    // replace assume
    return z;
  }
  while (x >= z) 
  /*
    infer [@term]
    requires true
    ensures x<z & z'=z & flow __norm or
            eres::ret_int<z> & x>=z & y<=0 & z'=z & flow __RET or
            x>=z & y>0 & z'>z & flow __norm;
  */
  /*@
    infer [@term]
    case {
      x<z -> ensures z'=z & flow __norm;
      x>=z -> case {
        y<=0 -> ensures eres::ret_int<z> & z'=z & flow __RET;
        y>0 -> ensures z'>z & flow __norm;
      }
    } 
  */
  /*
    infer [@post_n]
    case {
      x<z -> ensures true & flow __norm;
      x>=z -> case {
        y<=0 -> ensures true & flow __RET;
        y>0 -> ensures true & flow __norm;
      }
    }
  */
  {
    if(y <= 0) {
      // replace assume
      return z;
      // break;
    }
    z = z + y;
  }
  return z;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
