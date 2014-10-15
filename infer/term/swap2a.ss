// This example seems hard to handle by our
// current termination logic system.

ranking r(int x,int y).

int rotate(int i) 
  requires 0<=i<=1
  ensures i=0 & res=1 | i=1 & res=0;

  int swap (int x, int y,int z)
//infer[r]
 requires 0<=z<=1
 case {
  x=0 -> requires Term[] ensures true;
  x<0 -> 
   case {
    y<0 -> requires Loop[] ensures false;
    y=0 -> requires Term[] ensures true;
    y>0 -> requires Term[2*y+z] ensures true;
    }
   x>0 ->
     case {
      y<0 -> requires Term[2*x+z] ensures true;
      y=0 -> requires Term[] ensures true;
      y>0 -> requires Term[x+y] ensures true;
  }
 }
{
  z = rotate(z);
   if (x!=0) 
     return swap(y, x-1,z);
	else 
      return y;
}
