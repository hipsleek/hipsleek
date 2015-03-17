void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	gcd(x, y);
}

int gcd (int a, int b)
requires Term
ensures true;
{
	int tmp;
	while (b > 0 && a > 0)
	case {
		!(a>0 & b>0) -> requires Term ensures true;
		(a>0 & b>0) -> requires Term[b] ensures true;
	}
	{
		tmp = b;
		b = mod(a, b);
		a = tmp;
	}
	return a;
}

int mod (int a, int b)
requires Term
case {
	(a>=b & b<=0) -> ensures res=a;
	!(a>=b & b<=0) -> ensures res<b;
}
{
	while (a >= b && b > 0)
	case {
		a<b -> requires Term ensures a'=a & b'=b & a'<b';
		a>=b -> case {
			b<=0 -> requires Term ensures a'=a & b'=b;
			b>0 -> requires Term[a-b] ensures a'<b' & b'=b;
		}
	}
	{
		a = a - b;
	}
	return a;
}

int rand_int ()
requires Term
ensures true;

