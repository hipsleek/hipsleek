void loop(ref int x)
	requires x>11
	ensures x'=10;
	//variance x;
	requires x<=11
	ensures x'=x-1;
	//requires true
	//ensures (x>11 & x'=10) || (x<=11 & x'=x-1);
{ 
	int orig_x=x;
	x=x-1;
	if (x>10) {
      		//assert x>10 & orig_x-x>0;
		//assume false;
      		loop(x);
		assume x'=10;
		return;
   	}
	else return;
}

