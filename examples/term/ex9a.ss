
void loop(ref int x, ref int y, int N)
 case {
  x>N -> ensures "l1":x'=x & y'=y;
  x<=N -> requires x+y>0
         //variance N-x;
		  ensures "l2":true;
         requires x+y>=0
         //variance x+y>0;
		  ensures "l3":true;
 }
{
  if (x<=N) {
    bool b;
    b = randBool();
    if (b) {
      //assume x'>=2*x+y;
      //assume y'>=y+1;
 	  //if (x + y > 1)
      update1(x,y);
      //assert "l2":x'+y'>=0;
      //assert "l2":x'+y'>0;
      assert "l2":(N-x)-(N-x')>0;
      assert "l2":true  & (x'>N | N-x'>=0 ); // | (x'>N));
	  //x = 2*x + y;
	  //y = y + 1;
      assert "l3":x'+y'>0;
	  loop(x,y,N);
    } else {
      //assume x'>=x+1;
	  //assume y'=y;
      update2(x);
      assert "l3":(N-x)-(N-x')>0;
      assert "l3":true  & (x'>N | N-x'>=0 ); // | (x'>N));
      loop(x,y,N);
    }
  }
}

bool randBool()
  requires true
  ensures true;

void update1(ref int x, ref int y)
  requires true
  ensures x'>=2*x+y & y'>=y+1;

void update2(ref int x)
  requires true
  ensures x'>=x+1;


