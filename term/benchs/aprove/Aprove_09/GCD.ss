int rand_int ()
requires Term
ensures true;

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
	while (b != 0)
	case {
		b=0 -> requires Term ensures true;
		b!=0 -> case {
			(a<=0 | b<=0) -> requires Term ensures true;
			!(a<=0 | b<=0) -> case {
				a=b -> requires Term ensures true;
				a>b -> case {
					exists (k: a=k*b) -> requires Term ensures true;
					!(exists (l: a=l*b)) -> requires Term[b] ensures true;
				}
				a<b -> requires Term ensures true;
			}
		}
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
	(a<=0 | b<=0) -> ensures res=0;
	!(a<=0 | b<=0) -> case {
		a=b -> ensures res=0;
		a!=b -> case {
			a<=b -> ensures res<b;
			a>b -> case {
				exists (m: a=m*b) -> ensures res=b;
				!(exists (n: a=n*b)) -> ensures res<b;
			}
		}
	}
}
/*
{
	if (a <= 0 || b <= 0)
		return 0;
	if (a == b)
		return 0;
	while (a > b) 
	case {
		a<b -> requires Term ensures a'<b' & b'=b;
		a=b -> requires Term ensures a'=b' & b'=b;
		a>b -> case {
			b<=0 -> requires Loop ensures false;
			b>0 -> case {
				exists (k: a=k*b) -> requires Term ensures a'=b' & b'=b;
				!(exists (l: a=l*b)) -> requires Term[a] ensures a'<b' & b'<b;
			}
		}
	}
	{
		a = a - b;
	}
	return a;
}
*/
