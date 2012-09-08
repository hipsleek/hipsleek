void loop (int x)

requires true
ensures true;

//EXPECT SPEC
/*
case {
	x<=0 -> requires Term ensures true;
	x>0 -> requires Loop ensures false;
}
*/
{
	if (x<=0) return;
	else {
		loop(x-1);
		if (x<2)
			loop(x+1);
		else
			loop(x-1);
	}
}
