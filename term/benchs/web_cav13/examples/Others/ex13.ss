void loop (ref int x, ref int y)
case {
	x < y -> requires Term ensures true;
	x = y -> requires Loop ensures false;
	x > y -> requires MayLoop ensures true;
	/*
	x > y -> case {
		x>1 -> requires Term[x-y] ensures true;
		x<=1 -> requires Term[1-x] ensures true;
	}
	*/
}
{
	if (x > y) {
		y = x + y;
		x = x + 1;
		loop(x, y);
	} else if (x == y) 
		loop(x, y);
	else return;
}
