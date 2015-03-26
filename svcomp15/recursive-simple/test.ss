/* class Error extends __Exc { */
/*   int val; */
/* } */

void __error()
  requires true
  ensures true & flow __Error;


void f(int n)
//  infer [@flow,@post_n]
  requires true
  ensures n<3 & flow __norm or n>=3 & flow __Error;
{
  if (n<3) return;
  else {
    n--;
    f(n);
    //raise new Error(-1);
    __error();
  }
}

/* void main() */
/* //infer [@flow,@post_n] */
/*   requires true */
/*   ensures true ; */
/* { */
/*   f(3); */
/* } */
