void loop (int x, int y)

requires true
ensures true;

/*
case {
	x<=0 -> requires Term ensures true;
	x>0 -> case {
		x+y<=0 -> requires Term ensures true;
		x+y>0 -> requires Term[2*x+y] ensures true;
	}
}
*/
{
	if (x<=0) return;
	else loop (x+y, -1-y);
}

