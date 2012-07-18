void main (int n)
requires n>0 & Loop
ensures false;
{
	if (n > 0) {
		while (true)
			requires Loop ensures false;
		{ n = n; }
		main(n - 1);
	}
}
