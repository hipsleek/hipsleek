void loop(ref int x, ref int y, int N)
case {
  x>N ->	ensures "l1":x'=x & y'=y;
  x<=N ->	requires x+y>0
			variance (1) [N-x]
			ensures "l2":true;
			requires x+y>=0
			//variance 0 ==> x+y>0;
			ensures "l3":true;
 }
{
  if (x<=N) {
    bool b;
    b = randBool();
    if (b) {
      update1(x,y);
	  loop(x,y,N);
    } else {
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


