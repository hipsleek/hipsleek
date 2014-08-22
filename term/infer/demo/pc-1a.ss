void loop (int x, int y) 
//requires true
//ensures true;

case {
	x>0 -> requires true ensures true;
	x<=0 -> requires true ensures true;
}

{
	if (x<=0) return;
	else loop(x+y, y-1);
}
