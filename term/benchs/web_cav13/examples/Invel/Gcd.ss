/*
The following program only terminates when
	a = (F(n+1)/F(n)) * b, n > 0
where F(n) is the n-th Fibonacci number.
*/
int gcd (int a, int b)
requires MayLoop
ensures true;
{
	int t = 0;
	if (b > a) {
		t = a;
		a = b;
		b = t;
	}
	while (b != 0) 
	case {
		b!=0 -> case {
			a!=b -> case {
				a=b+b -> requires Term ensures true;
				a!=b+b -> case {
					2*a=3*b -> requires Term ensures true;
					2*a!=3*b -> requires MayLoop ensures true;
				}			
			}
			a=b -> requires Term ensures true;
		}
		b=0 -> requires Term ensures true;
	}
	{
		t = a - b;
		a = b;
		b = t;
	}
	return a;
}
