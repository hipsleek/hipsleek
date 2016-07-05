/* zip - numeric */


void error()
  requires false
  ensures true;

relation R(int a,int b,int c).
relation P(int a,int b).

int zip(int x, int y)
  infer [R]
  requires x>=0 & y>=0 & P(x,y)
  ensures  R(res,x,y);

/*
Sound we have a WARNING that unknown P is not
in the inferred list?

Great to have this failure!

Context of Verification Failure: File "n-z-1d-2.ss",Line:13,Col:11
Last Proving Location: File "n-z-1d-2.ss",Line:32,Col:7

ERROR: at n-z-1d-2.ss_32_7 
Message: Proving precondition in method failed.

*/

{
  if (x==0) return 0;
  else {
    if (y==0) {
       error();
       return -1;
    }
    else 
      return 1+zip(x-1,y-1);
  }
}










