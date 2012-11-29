void increase (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Loop ensures false;
}
{
	if (i > 0) {
		if (i % 2 == 0)
			i--;
		else
			i = i + 3;
		increase(i);
	}
}
