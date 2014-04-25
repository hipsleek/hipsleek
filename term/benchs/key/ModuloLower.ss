void loop (int n)
case {
	n<=2 -> requires Term ensures true;
	n>2 -> case {
		n<5 -> requires Term[n] ensures true;
		n>=5 -> requires Loop ensures false;
	}
}
{
	if (n > 2) {
		if (n % 5 > 0) {
			n--;
		}
		loop(n);
	}
}
