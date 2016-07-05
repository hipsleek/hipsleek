void increase (int i)
case {
	i>=10 -> requires Term ensures true;
	i<10 -> case {
		i<=3 -> requires Loop ensures false;
		i>3 -> requires Term[10-i] ensures true;
	}
}
{
	if (i < 10) {
		if (i != 3) {
			i++;
		}
		increase(i);
	}
}
