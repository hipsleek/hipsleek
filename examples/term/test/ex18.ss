// McCarthy 91
int f(int x)
ensures true;
{
	int s = 1;
	return loop(x, s);
}

int loop(int x, int s)
requires s>=1
case {
	//Lexicographical ranking function <10s-x+90,x>
	x>100 -> case {
				s=1 -> ensures "l1":true;
				s!=1 -> variance (1) [10*s-x+90,x]
						ensures "l2":true;
			 }
	x<=100 ->	variance (1) [10*s-x+90,x]
				ensures "l3":true;
}
{
	int x1, s1;
	if (x > 100) {
		if (s == 1) return x - 10;
		else {
			x1 = x - 10;
			s1 = s - 1;

			return loop(x1, s1);
		}
	} else {
		x1 = x + 11;
		s1 = s + 1;

		return loop(x1, s1);
	}
}	