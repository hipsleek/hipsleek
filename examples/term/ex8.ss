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
x>=0 -> requires x>5
        ensures x'<0;
}

{
	if (x >= 0) {
		x = -2*x + 10;
		//if (x >= 0) 
        loop(x);
	}
}
