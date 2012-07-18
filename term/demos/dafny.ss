void main (int n)
requires n>0 & Term[n]
ensures true;
{
	if (n > 0) {
		while (true)
			requires Loop ensures false;
		{ n = n; }
		main(n - 1);
	}
}
