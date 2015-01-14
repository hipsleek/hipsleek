void test (int n)
case {
	n>0 -> requires Term[2*n] ensures true;
	n<=0 -> requires Term[1] ensures true;
}
{
	int i = n - 1;
	loop(i);
}

void loop (int i)
case {
	i<0 -> requires Term ensures true;
	i>=0 -> requires Term[2*i+1] ensures true;
}
{
	if (i >= 0) {
		test(i);
		i--;
		loop(i);
	}

}

void main ()
requires Term
ensures true;
{
	test(10);
}
