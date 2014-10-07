
int gcd (int a, int b)
requires true
ensures true;
{
	int t = 0;
	if (b > a) {
		t = a;
		a = b;
		b = t;
	}
	while (b != 0) 
	requires MayLoop
	ensures true;
	{
		t = a - b;
		a = b;
		b = t;
	}
	return a;
}
