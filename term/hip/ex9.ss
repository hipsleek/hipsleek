void loop(ref int x, ref int y, int N)
case {
  x>N -> variance [0,0] ensures "l1": x'=x & y'=y;
  x<=N -> requires x+y>0
          variance [0,1,N-x]
          ensures "l2": N-x'<0;
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
      update1(x,y);
      loop(x,y,N);
    } else {
      //assume x'>=x+1;
	  //assume y'=y;
	  update2(x);
      loop(x,y,N);
    }
  }
}

bool randBool()
  requires true
  ensures true;
  
// update x,y to x'>=2*x+y & y'>=y+1;
void update1(ref int x, ref int y)
  requires true
  ensures x'>=2*x+y & y'>=y+1;

// update x to x'>=x+1;
void update2(ref int x)
  requires true
  ensures x'>=x+1;
