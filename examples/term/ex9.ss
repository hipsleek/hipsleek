
void loop(ref int x, ref int y, int N)
 case {
  x>N -> ensures "l1":x'=x & y'=y;
  x<=N -> requires x+y>0
          // variance ?
          ensures "l2":N-x'<0;
 }
{
  if (x<=N) {
    bool b;
    //dprint;
    b = randBool();
    //dprint;
    if (b) {
      //assume x'>=2*x+y;
      //assume y'>=y+1;
      //dprint;

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
