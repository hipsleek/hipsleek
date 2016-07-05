void loop(ref int x)
case {
  x<0 -> requires Term ensures "r1": x'=x;
  x>=0 -> case {
		x>5 -> requires Term ensures "r2": x'<0;
		x<=2 -> requires Term ensures "r3":x'<0;
		x=3 -> requires Term ensures "r4": x'<0;
		4<=x<=5 -> requires Term ensures "r8":x'<0;
   }
}
{
	if (x >= 0) {
		//x = -2*x + 10;
		x = -(x+x) + 10;
    assert "r2":x-x'>0;
    assert "r2":x'>=0; //not well-founded! // fails
    assert "r2":x'<0;  //going to base case
    assert "r3":x'>5; //going to another base case
    assert "r8":x'<=2; //going to another base case
    assert "r4":x'=4; //going to another base case
		//if (x >= 0) 
    loop(x);
	}
}

void loop2(ref int x)
case {
	x<0 -> requires Term ensures "r1": x'=x;
 	x>=0 -> case {
		x>10 -> requires Term ensures "r2": x'<0;
    x<=10 -> requires Loop ensures "r3":false;
 }
}

{
	if (x >= 0) {
		x = -x + 10;
		//if (x >= 0)
    assert "r2": x-x'>0;
    assert "r2": x'<0;
    loop2(x);
  }
}
