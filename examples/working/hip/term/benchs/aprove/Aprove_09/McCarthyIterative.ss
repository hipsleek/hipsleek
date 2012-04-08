int mcCarthy (int x)
case {
	x>100 -> requires Term ensures res=x-10;
	x<=100 -> requires Term ensures res=91;
}
{
	int c = 1;
	while (c > 0) 
	case {
		c<=0 -> requires Term[] ensures x'=x & c'=c ;
    c=1 -> case {
			x>100 -> requires Term[] ensures x'=x-10 & c'=0 ;
			x<=100 -> requires Term[200+21*c-2*x]  ensures x'=91 & c'=0 ;
    }
    c>1 -> 
      requires x<=111 & Term[200+21*c-2*x]
      ensures x'=91 & c'=0;
}
	{
		if (x > 100) {
			x = x - 10;
			c--;
		} else {
			x = x + 11;
			c++;
		}
	}
	return x;
}
