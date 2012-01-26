// CHOICE Lin Transition Invariant paper

bool rand()
  requires true
  ensures true;

void loop1(int y, int x)
 case {
     x>0 & y> 0 -> ensures true;
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
  }
}

