void increase (int i)
/*
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Loop ensures false;
}
*/
requires true
ensures true;
{
	if (i > 0) {
		i++;
		increase(i);
	}
}
