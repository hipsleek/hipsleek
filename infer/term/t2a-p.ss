
// CHOICE in Transition Invariant paper
//Termination: Contradiction in Phase Constraints.
//Termination checking result:
// Please use the same phase!
logical int p1,p2,p3,p4;

bool rand()
  requires Term[]
  ensures true;

void loop1(int y, int x)
 case {
     x>0 & y>0 ->
   case {
       x=y-1 -> requires Term[p1] ensures true;
       x=y-2 -> requires Term[p2] ensures true;
       ((x!=y-1) & (x!=y-2)) -> requires Term[p3] ensures true;
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

