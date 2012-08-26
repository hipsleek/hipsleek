void loop (int x, int y)
case {
	x>=5 -> requires Term ensures true;
	x<5 -> case {
		x<y -> case {
			y>4 -> requires Term[5-x] ensures true;
			y<5 & y>=1 -> requires Loop ensures false;
			y<1 -> requires Term[5-x] ensures true;
		}
		x=y -> case {
			y>1 -> requires Loop ensures false;
			y=1 -> requires Loop ensures false;
			y<1 -> requires Term ensures true;
		}
		x>y -> requires Term[5-x] ensures true;
	}
}
{
	if (x >= 5) return;
	else {
		if (x == y) x = 0;
		x = x + 1;
		loop(x, y);
	}
}
