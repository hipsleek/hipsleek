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
	while (a > 0 && b > 0)
	case {
		a>0 -> case {
			b<=0 -> requires Term ensures true;
			b>0 -> requires Term[b] ensures true;
		}
		a<=0 -> requires Term ensures true;
	}
	{
		tmp = b;
		b = a % b; // a % b < b
		a = tmp;
	}
	return a;
}
