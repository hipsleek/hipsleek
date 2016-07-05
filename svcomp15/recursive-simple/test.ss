/* class Error extends __Exc { */
/*   int val; */
/* } */

void __error()
  requires emp & true
  ensures emp & true & flow __Error;


void f(int n)
//  infer [@flow,@post_n]
 case {
  n<3 -> ensures emp & true;
  n>=3 -> ensures emp & true & flow __Error;
}
{
  //dprint;
  if (n<3) return;
  else {
    n--;
    //  dprint;
    f(n);
    //raise new Error(-1);
    // dprint;
    __error();
    // dprint;
  }
}

void main() //(int n)
//infer [@flow,@post_n]
  requires true
  ensures true ;
{
  //f(n);
  f(2);
  //f(3);
  //dprint;
}
