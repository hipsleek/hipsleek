void loop (int i)
case {
	i<=5 -> requires Term ensures true;
	i>5 -> case {
		i<10 -> requires Term[i] ensures true;
		i>=10 -> requires Loop ensures false;
	}
}
{
	if (i > 5) {
		if (i != 10)
			i--;
		loop(i);
	}
}
