void loop(ref int x, int y)
case {
  x<=0 -> 
    // variance 0 // no-recursive call
    ensures x'=x; //'
   x>0 -> //ensures true;
   case {
         y>=0 -> 
           // variance -1 // non-termination
           ensures false;
         y<0 -> 
           // variance x
           ensures x'<x & x'<=0;
        }
 
 }
{
  if (x>0) {
      x=x+y; 
      loop(x,y); 
  }
}
