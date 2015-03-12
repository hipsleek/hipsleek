/* -tp redlog */
int fact (int n) 
	requires n >= 0 & Term[n] or n < 0 & Loop
	ensures true;
{
	if (n == 0) return 1;
	else return n * fact(n - 1);
}
