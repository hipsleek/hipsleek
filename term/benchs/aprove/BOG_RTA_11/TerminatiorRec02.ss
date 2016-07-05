//Factorial example

int fact (int x)
case {
	x<=1 -> requires Term ensures true;
	x>1 -> requires Term[x] ensures true;
}
{
	if (x > 1) {
		int y = fact(x - 1);
		return y * x;
	}
	return 1;
}
