void decrease (int i)
case {
	i<=5 -> requires Term ensures true;
	i>5 -> requires Term[i] ensures true;
}
{
	if (i > 5) {
		i--;
		decrease(i);
	}
}
