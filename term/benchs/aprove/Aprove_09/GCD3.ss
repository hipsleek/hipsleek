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
case {
	b=0 -> requires Term ensures res=0;
	b<0 -> case {
		a<0 -> requires Loop ensures false;
		a=0 -> requires Term ensures res=0;
		a>0 -> requires Term ensures res<(-b);
	}
	b>0 -> case {
		a>0 -> requires Term ensures res<b;
		a=0 -> requires Term ensures res=0;
		a<0 -> requires Loop ensures false;
	}
}
{
	if (b == 0) {
		return b;
	}
	if (b < 0) {
		a = -a;
	}
	if (a > 0) {
		while (a >= b) 
		case {
			a<b -> requires Term ensures a'<b' & a'=a & b'=b;
			a>=b -> case {
				b>0 -> requires Term[a-b] ensures a'<b & b'=b;
				b<=0 -> requires Loop ensures false;
			}
		}
		{
			a = a - b;
		}
		return a;
	} else {
		while (a < 0) 
		case {
			a>=0 -> requires Term ensures a'=a & b'=b;
			a<0 -> case {
				b>=0 -> requires Loop ensures false;
				b<0 -> requires Term[-a] ensures a'<(-b') & b'=b;
			}
		}
		{
			a = a - b;
		}
		return a;
	}
}

int rand_int ()
requires Term
ensures true;

