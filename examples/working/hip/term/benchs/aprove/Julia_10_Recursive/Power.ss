int power (int a, int n) 
case {
	n<=1 -> requires Term ensures true;
	n>1 -> requires Term[n] ensures true;
}
{
	if (n <= 0) return 1;
	else if (n == 1) return a;
	else {
		int r = power(a * a, n/2);
	  if (n % 2 == 0) return r;
	  else return a * r;
	}
}

