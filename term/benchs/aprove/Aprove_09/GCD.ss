int rand_int ()
requires Term
ensures true;
/*
void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();

	gcd(x, y);
}
*/
/*
int gcd (int a, int b)
requires Term
ensures true;
{
	int tmp;
	while (b != 0)
	case {
		(a=b | a<=0 | b<=0) -> requires Term ensures true;
		!(a=b | a<=0 | b<=0) -> requires MayLoop ensures true; 
	}
	{
		tmp = b;
		b = mod(a, b);
		a = tmp;
	}
	return a;
}
*/
int mod (int a, int b)
requires Term
case {
	(a=b | a<=0 | b<=0) -> ensures res=0;
	!(a=b | a<=0 | b<=0) -> ensures res<=b; 
}
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
			b>0 -> requires Term[a] 
				case {
					exists (k: a=k*b) -> ensures a'=b' & b'=b;
					!(exists (l: a=l*b)) -> ensures a'<=b' & b'=b;
				}
		}
	}
	{
		a = a - b;
	}
	return a;
}
