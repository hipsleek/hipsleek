
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
     a<b -> case {
              x>0 -> requires Term[x] ensures true;
              x<=0 -> requires MayLoop ensures true;
             }
     a>b -> 
            case {
              y>0 -> requires Term[y] ensures true;
              y<=0 -> requires MayLoop ensures true;
             }
     }
   x<=0 & y<=0 ->
     requires Term[] ensures true;
 }
{
  if (x>0 || y>0) {
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex20c.ss

 case {
   x>0 | y>0 -> 
    case {
     a=b -> requires Term[x]
       ensures true;
     a!=b -> requires MayLoop
             ensures true;
     }
   x<=0 & y<=0 ->
     requires Term[] ensures true;
 }

# how to handle:

Termination checking result: 
(24)->(36) (MayTerm ERR: not bounded)[x]

 */
