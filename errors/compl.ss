
float sqrt(float x)
 case {
   x>=0.0 -> ensures (x=res*res);
   x<0.0  -> ensures true & flow __Error;
}
//res*res*res*res + 2.0*res*x - 2.0*res*y + x*x + y*y + 2.0*x*y=0.0
float foo(float x, float y)
 case {
   y >= 0.0 -> case {
     x >= 0.0 -> ensures (x=res*res);
     x < 0.0 -> ensures (exists a, b: (res = a + b) & (y = a*a) & (x + b*b = 0.0));
   }
   y < 0.0 -> ensures (true) & flow __Error;
 }
 {
  float r = sqrt(y);

  if (x>=0.0){
     return sqrt(x);
  }
  else {
    return sqrt(0.0-x)+r;
  }
 }
/*
float sine(float x)
 case {
  x>=0.0 & x <= 3.14 -> ensures (res>=0.0) & (res <1.0);
  x<0.0  & x >= (0.0 - 3.14) -> ensures (res <0.0) & (res >= (0.0 - 1.0));
  (x> 3.14 | x < (0.0 - 3.14)) -> ensures (true) & flow __Error;
}
*/
/*
  requires true
  ensures  -1 <= res <= 1;  //is this correct?
*/
/*
float foo1(float x, float y)
 case {
   y >= 0.0 -> case {
     x >= 0.0 & x <= 3.0 -> ensures (x=res*res);
     x<0.0  & x >= (0.0-3.0)  -> ensures (exists a, b: (res = a + b) & (y = a*a) & (x + b*b = 0.0));
     x> 3.0  -> ensures true & flow __Error;
     x < (0.0 - 3.0) -> ensures true & flow __Error;
   }
   y < 0.0 -> ensures (true) & flow __Error;
 }
{
  float r = sqrt(y);
  if (sine(x)>=0.0)
           return sqrt(x);
  else
    return sqrt(0.0 - x)+r;
}

*/
