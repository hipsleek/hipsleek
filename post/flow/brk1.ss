int main(int x)
//infer [@flow,@post_n]
  requires true
  ensures true;// & flow __flow;
{
  while (x > 0)
    //infer [@post_n,@flow]
    requires true
      ensures x>=1 & x'=0 or x'>=2223 & x'=x or x'<=0 & x=x';
    // ensures true & flow __flow;
    // ensures x'<=x & x'<=0 & flow __norm or eres::ret_int<1> & x=x' & 2223<=x' & flow ret_int;
    //ensures x'=x;
    //ensures (x>2222 | x<=0) & x'=x or 0<x & x<=2222 & x'=0;
    //ensures  true & flow __flow;//x'<=x & x'<=0 & flow __norm or x'=x & eres::ret_int<2> & flow ret_int;
//true & flow __flow;
    {
      if (x > 2222) {
        //break;
        return 1;
      } else {
        x = x - 1;
      }
    }
  return 0;
}
