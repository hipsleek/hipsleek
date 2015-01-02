int avg (int x, int y)
case {
	x>1 -> requires Term[x] ensures true;
	x=0 -> case {
		y>2 -> requires Term[x+y, x] ensures true;
		y<=2 -> requires Term[0] ensures true;
	}
	x=1 -> case {
		y>1 -> requires Term[x+y, x] ensures true;
		y<=1 -> requires Term[1] ensures true;
	}
	x<0 -> case {
		y<=2 -> requires Term ensures true;
		y>2 -> requires Term[-x] ensures true;
	}
}
{
	if (x > 0)
		return avg(x-1, y+1);
	else if (y > 2)
		return 1 + avg(x+1, y-2);
	else
		return 1;
}

