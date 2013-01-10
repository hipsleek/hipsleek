void half (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Loop ensures false;
}
{
	int l = i;
	i = 0;
	loop(i, l);
}

void loop (ref int i, ref int l)
case {
	l<=i -> requires Term ensures true;
	l>i -> requires Loop ensures false;
}
{
	if (l - i > 0) {
		i = i + (l - i) / 2;
		loop(i, l);
	}
}
