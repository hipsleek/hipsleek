void increase (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Loop ensures false;
}
{
	if (i > 0) {
		i++;
		increase(i);
	}
}
