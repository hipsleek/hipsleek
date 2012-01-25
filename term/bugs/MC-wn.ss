int mcCarthy (int x)
requires x<=111
case {
	x>100 -> ensures res=x-10;
	x<=100 -> ensures res=91;
}
{
	int c = 1;
	loop(x, c);
	return x;
}

void loop (ref int x, ref int c)
requires x<=111
case {
	c<=0 -> requires Term[] ensures x'=x & c'=c ;
    c=1 ->
      case {
		x>100 -> requires Term[] ensures x'=x-10 & c'=0 ;
		x<=100 -> requires Term[1,111-x,c] ensures x'=91 & c'=0 ;
	}
    c>1 ->
      case {
      x>100 -> requires Term[1,111-x,c] ensures x'=91 & c'=0 ;
      x<=100 -> requires Term[1,111-x,c] ensures x'=91 & c'=0 ;
	 }
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
