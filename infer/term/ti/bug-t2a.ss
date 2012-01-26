// CHOICE in Transition Invariant paper
//Termination: Contradiction in Phase Constraints.
//Termination checking result:
// Please use the same phase!

bool rand()
  requires Term[]
  ensures true;

void loop1(int y, int x)
 case {
     x>0 & y>0 ->
   case {
       x=y-1 -> requires Term[x,1] ensures true;
       x=y-2 -> requires Term[x,2] ensures true;
       ((x!=y-1) & (x!=y-2)) -> requires Term[x+y] ensures true;
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
