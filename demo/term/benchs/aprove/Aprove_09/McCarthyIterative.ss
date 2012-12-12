int mcCarthy (int x)
case {
	x>100 -> requires Term ensures res=x-10;
	x<=100 -> requires Term ensures res=91;
}
{
	int c = 1;
	loop(x, c);
	return x;
}

void loop (ref int x, ref int c)
case {
	c<=0 -> requires Term ensures x'=x & c'=c;
	c>=1 -> case {
		x>100 -> requires Term ensures x'=x-10 & c'=c-1;
		x<=100 -> requires MayLoop ensures x'=91 & c'=c+1;
	}
    //	c>1 -> requires MayLoop ensures x'=91;
}
{
	if (c > 0) {
		if (x > 100) {
			x = x - 10;
			c--;
		} else {
			x = x + 11;
			c++;
		}
		loop(x, c);
	}
}
