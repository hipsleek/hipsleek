void loop(ref int x)
/*
case {
	x < 0 -> 
		//variance 0
		ensures x' = x;
	x >= 0 & x <= 5 ->
		//variance -1
		ensures false;
	x > 5 ->
		ensures x' < 0;
}
*/
//requires x < 0
//ensures x' = x;

//requires x >= 0 & x <=3
//ensures false;

//requires x > 5
//ensures x'<0;
case {
 x<0 -> ensures x'=x;
x>=0 -> case {
         x>5 -> ensures x'<0;
        x<=5 -> ensures true;
       }
}

{
	if (x >= 0) {
		x = -2*x + 10;
		//if (x >= 0) 
        loop(x);
	}
}

void loop2(ref int x)
/*
  requires x=0 or x=10
  ensures false;
  requires x=1 or x=9
  ensures false;
 requires x=2 or x=8
  ensures false;
 requires x=3 or x=7
  ensures false;
requires x=4 or x=6
  ensures false;
requires x=5
  ensures false;
*/
 case {
  x<0 -> ensures "r1": x'=x;
 x>=0 -> case {
           x>10 -> 
          //variance x
          ensures "r2":x'<0;
  x<=10 -> ensures "r3":false;
 }}

{
	if (x >= 0) {
		x = -x + 10;
		//if (x >= 0)
        assert "r2": x-x'>0;
        assert "r2": x'<0;
        loop2(x);
	}
}

