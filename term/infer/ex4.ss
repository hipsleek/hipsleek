void loop (int x) 
/*
case {
	x=0 -> requires Term ensures true;
	x!=0 -> case {
		x=2 -> requires Term ensures true;
		x!=2 -> requires Loop ensures false;
	}
}
*/
requires true
ensures true;
{
	if (x==0) return;
	else loop(2-x);
}
