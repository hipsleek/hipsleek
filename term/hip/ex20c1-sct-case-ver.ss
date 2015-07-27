
/*
int x, y, a, b; // all init as nondet();
if (a != b) { return; }
// a == b
while (x > 0 || y > 0) {
  x = x + a - b - 1;
  y = y + b - a - 1;
}
*/

// above cannot be handled by normal size-change..


     /*
      case {
       x>y -> requires Term[x]
              ensures true;
       x<=y -> requires Term[y]
       ensures true;
      }
     */

void loo (ref int x, ref int y,int a, int b)
 case {
   a=b ->
     case {
      x>0 | y>0 -> requires Term[max(x,y)] ensures true;
      x<=0 & y<=0 -> requires Term[] ensures true;
     }
   a<b ->
     case {
      x>0  -> 
        //requires MayLoop ensures true;
        case {
        x-y<b-a+1 -> requires Term[x+y] ensures true;
        x-y>=b-a+1 -> requires MayLoop ensures true;
        
        }
      //x>0 & y<=0 -> requires MayLoop ensures true;
      x<=0 & y>0 -> requires Loop ensures false;
      x<=0 & y<=0 -> requires Term[] ensures true;
     }
   a>b ->
     case {
      x>0 & y>0 -> requires MayLoop ensures true;
      x<=0 & y>0 -> requires MayLoop ensures true;
      x>0 & y<=0 -> requires Loop ensures false;
      x<=0 & y<=0 -> requires Term[] ensures true;
     }
 }
{
  if (x>0 || y>0) {
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex20c1.ss

   a<b ->
     case {
      x>0 & y>0 -> requires MayLoop ensures true;
      x>0 & y<=0 -> requires MayLoop ensures true;
      x<=0 & y>0 -> requires Loop ensures false;
      x<=0 & y<=0 -> requires Term[] ensures true;
     }

# MayLoop can be refine to some terminating scenario..


 */
