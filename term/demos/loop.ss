void loop (ref int x, ref int y, ref int n)
case {
	n=0 -> requires Term ensures x'=x & y'=y & n'=n;
	n>0 -> requires x=2*y & Term[n] ensures x'=2*y' & n'=0;
	n<0 -> requires Loop ensures false;
}
{
	if (n == 0) return;
	else {
		x = x + 2;
		y = y + 1;
		n = n - 1;
		return loop(x, y, n);
	}
}

void main() 
requires MayLoop
ensures true;
{
	int x = 0, y = 0;
	int n = input();
	loop(x, y, n);
}

int input()
requires Term
ensures true;
