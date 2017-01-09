int test_fun(int x, int y)
{
  int c = 0;
  //if(x <= 0 || y <= 0) {
    // replace assume
    //return x + y;
  //}
  while (!(x == 0)) 
    case {
      (x<0 & x<=y) | (x>y & y<=0 & x!=0) -> ensures eres::ret_int<x'> & flow __RET;
      !((x<0 & x<=y) | (x>y & y<=0 & x!=0)) -> ensures true & flow __norm;
    }
  {
    if (x > y) {
      x = y;
    } else {
      if(x <= 0) {
        // replace assume
        return x;
      }
      x = x - 1;
    }
    c = c + 1;
  }
  return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}

/*
void loop (int x, int y)
/*
  case {
    (x=0 | (x<0 & x<=y)) -> requires Term[74,1] ensures emp & true; 
    y<x & 1<=x -> requires Term[74,3] ensures true; 
    y<x & x<=(0-1) -> requires Term[74,4] ensures true; 
    1<=x & x<=y -> requires Term[74,2,x] ensures true; 
  }
*/
{
  if (x != 0) {
    if (x > y) {
      x = y;
    } else {
      if (x <= 0) {
        return;
      }
      x = x - 1;
    }
    loop(x, y);
  }
}
*/
