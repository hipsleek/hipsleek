/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)

// Why isn't parameter mismatch checking done?

  infer [R]
  requires 0<=x<=y
  ensures  R(res,x);

/*
Translating global variables to procedure parameters...
Stop Omega... 22 invocations caught

Exception occurred: Failure("gather_type_info_b_formula: error with relation R")
E

  requires 0<=x<=y
  ensures  res=x;
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










