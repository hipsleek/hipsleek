// This example seems hard to handle by our
// current termination logic system.

ranking r(int x,int y).


int swap (int x, int y)
//infer[r]
 case {
  x=0 -> requires Term[] ensures true;
  x<0 -> 
   case {
    y<0 -> requires Loop[] ensures false;
    y=0 -> requires Term[] ensures true;
    y>0 -> requires Term[2*y+1] ensures true;
    }
   x>0 ->
     case {
      y<0 -> requires Term[2*x] ensures true;
      y=0 -> requires Term[] ensures true;
      y>0 -> requires Term[x+y] ensures true;
  }
 }
{
   if (x!=0) 
     return swap(y,x-1);
	else 
      return y;
}

