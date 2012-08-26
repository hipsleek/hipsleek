void loop (int x, int y)
case {
	x<0 -> requires Term ensures true;
	x>=0 -> case {
		y>=0 -> requires Loop ensures false;
		y<0 -> case {
			x+y<0 -> requires Term ensures true;
			x+y>=0 -> requires Loop ensures false;
		}
	}
}
{
	if (x<0) return;
	else loop(x+y, 1-y);
}

void main ()
requires Loop
ensures false;
{
	int x = 1;
	loop(x, 0);
}
