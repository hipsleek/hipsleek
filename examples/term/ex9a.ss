
void loop(ref int x, ref int y, int N)
 case {
  x>N -> ensures "l1":x'=x & y'=y;
  x<=N -> requires x+y>0
         //ensures "l2":N-x'<0;
		  ensures "l2":true;
 }
{
  if (x<=N) {
    bool b;
    b = randBool();
    if (b) {
      //assume x'>=2*x+y;
      //assume y'>=y+1;
	  if (x + y > 0)
	   x = 2*x + y;
	  y = y + 1;
	  loop(x,y,N);
    } else {
      assume x'>=x+1;
	  assume y'=y;
      loop(x,y,N);
    }
  }
}

bool randBool()
  requires true
  ensures true;
