template int r(int n).

int mc91 (int n)
infer[r]
case {
	n>100 -> requires Term ensures res = n-10;
	n<=100 -> requires Term[r(n)] ensures res = 91;
}
{
	if (n > 100) return n-10;
	else return mc91(mc91(n+11));
}
