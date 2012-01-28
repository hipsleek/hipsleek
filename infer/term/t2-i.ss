// CHOICE in Transition Invariant paper
//Termination: Contradiction in Phase Constraints.
//Termination checking result:
// Please use the same phase!

ranking ra(int x).
ranking rb(int x).
ranking r2(int x, int y).

bool rand()
  requires Term[]
  ensures true;

void loop1(int y, int x)
  infer @pre [ra,rb,r2]
 case {
     x>0 & y>0 ->
   case {
       x=y-1 -> requires Term[0,ra(x)] ensures true;
       x=y-2 -> requires Term[0,rb(x)] ensures true;
       ((x!=y-1) & (x!=y-2)) -> requires Term[1,r2(x,y)] ensures true;
      }
  x<=0 | y<=0 -> requires Term[] ensures true;
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

