
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
      x>0 | y>0 -> 
        case { 
          a=b -> requires Term[max(x,y)] ensures true;
          a=b+1 -> 
           case {
            x>0 -> requires Loop ensures false;
            x<=0 -> requires Term[y] ensures true;
           }
          b=a+1 -> //requires MayLoop ensures true;
           case {
            y>0 -> requires Loop ensures false;
            y<=0 -> requires Term[x] ensures true;
           }
          a>b+1 -> 
          //requires MayLoop ensures true;
          /* not working  a-b>=2
           x++, y--  
               x --> x+(a-b)-1
               y --> y-1-(a-b) 
           a>=b+2
           b<=a-2
          */
          case {
            y>0 & x>0 -> requires Loop ensures false;
            y>0 & x<=0 -> requires MayLoop ensures true;
            /*
            case {
              y-x<a-b -> requires Term ensures true;
              y-x>=a-b -> requires MayLoop ensures true;
            }
            */
            y<=0 & x>0 -> requires Loop ensures false;
           }
          b>a+1 -> //requires MayLoop ensures true;
            //x--;y++
          case {
            y>0 & x>0 -> requires Loop ensures false;
            y<=0 & x>0 -> requires MayLoop ensures true;
            y>0 & x<=0 -> requires Loop ensures false;
           }
         }
      x<=0 & y<=0 -> requires Term[] ensures true;
 }
{

  if (x>0 || y>0) {
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex20c3.ss

   a<b ->
     case {
      x>0 & y>0 -> requires MayLoop ensures true;
      x>0 & y<=0 -> requires MayLoop ensures true;
      x<=0 & y>0 -> requires Loop ensures false;
      x<=0 & y<=0 -> requires Term[] ensures true;
     }

          a>b+1 -> requires MayLoop ensures true;
          b>a+1 -> requires MayLoop ensures true;

# MayLoop can be refine to some terminating scenario..


 */
