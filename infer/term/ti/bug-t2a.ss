// CHOICE in Transition Invariant paper
//Termination: Contradiction in Phase Constraints.
// Termination checking result:
// Please use the same phase!
/*
Termination: Contradiction in Phase Constraints.
Phase Constrs:[ p1>=p4, p1>=p2, p2>p1, p2>=p4, p2>=p1, p3>=p4, p3>=p1]

{p3},{p2,p1},{p4}
*/

logical int p1,p2,p3,p4;

bool rand()
  requires Term[]
  ensures true;

void loop1(int y, int x)
 case {
     x>0 & y>0 ->
   case {
       x=y-1 -> requires Term[p1,x] ensures true;
       x=y-2 -> requires Term[p2,x] ensures true;
       ((x!=y-1) & (x!=y-2)) -> requires Term[p3,x+y] ensures true;
      }
  x<=0 | y<=0 -> requires Term[p4] ensures true;
  }
{
  if (x>0 && y>0) {
    if (rand()) {
      y = x;
      x = x-1;
    } else {
      int t=x+1;
      x = y-2;
      y=t;
    }
    loop1(y,x);
  }
}

/*
(x,y) 
 -> (x-1,x)
     -> (x-2,x-1)
     -> (x-2,x)

 -> (y-2,x+1)
     -> (y-3,y-2)
         -> (y-4,y-3)
         -> (y-4,y-2)
     -> (x-1,y-1)


 (x-1,x) 
   --> (x-2,x-1)
   --> (x-2,x)

*/
