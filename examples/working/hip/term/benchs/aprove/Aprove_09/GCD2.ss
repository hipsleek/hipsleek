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
	while (b != 0 && a >= 0 && b >= 0)
	case {
		!(a>=0 & b>0) -> requires Term ensures true;
		(a>=0 & b>0) -> case {
			a=b -> requires Term ensures true;
			a>b -> case {
				exists (m: a=m*b) -> requires Term ensures true;
				!(exists (n: a=n*b)) -> requires Term[b] ensures true;
			}
			a<b -> requires Term ensures true;
		}
	}
	{
		tmp = b;
		b = mod(a, b);
		a = tmp;
	}
	return a;
}

int rand_int ()
requires Term
ensures true;

int mod (int a, int b)
case {
	a<b -> requires Term ensures res=a;
	a=b -> requires Term ensures res=0;
	a>b -> case {
		b<=0 -> requires Loop ensures false;
		b>0 -> requires Term
		case {
			exists (m: a=m*b) -> ensures res=b;
			!(exists (n: a=n*b)) -> ensures res<b;
		}
	}
}

/*
case {
	a<=b -> requires Term ensures res=0 | res=a;
	a>b -> case {
		b<=0 -> requires Loop ensures false;
		b>0 -> requires Term ensures res<=b;
	}
}
{
	if (a == b) {
		return 0;
	}
	while (a > b)
	case {
		a<=b -> requires Term ensures a'<=b' & a'=a & b'=b;
		a>b -> case {
			b<=0 -> requires Loop ensures false;
			b>0 -> requires Term[a-b] ensures a'<=b' & b'=b;
		}
	}
	{
		a = a - b;
	}
	return a;
}
*/
