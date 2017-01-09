/* Example suggested by Shengchao */

void f(int x, int y)

  infer [@term]
  requires true
  ensures true;
/*
 case {
   x>=1 -> case {
     y>=0 -> requires Loop ensures false;
     y<0 -> case {
       1<=x & x<=(-y-1 )-> requires Term[] ensures true;
       y<=-1 & -x+1<=y -> requires Loop ensures false;
       y=-x & 1<=x-> requires Term[] ensures true;
     }
   }
   x<=0 -> requires Term[] ensures true;
 }
*/
{
  if (x <= 0) return;
  else f(x + y, x + y);
}
/*
f:  case {
  1<=x -> case {
           0<=y -> requires emp & Loop[]
 ensures false & false; 
           y<=(0-
           1) -> case {
                  1<=x & x<=((0-y)-
                  1) -> requires emp & Term[29,5]
 ensures emp & true; 
                  ((0-x)+1)<=y & y<=(0-
                  1) -> requires emp & Loop[]
 ensures false & false; 
                  y=0-x & 
                  1<=x -> requires emp & Term[29,8]
 ensures emp & true; 
                  }
           
           }
  
  x<=0 -> requires emp & Term[29,1]
 ensures emp & true; 
  }
 */
