void loop (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> case {
		i>=5 -> requires Loop ensures false;
		i<5 -> requires Term[i] ensures true;
	}
}
{
	if (i > 0) {
		if (i != 5) {
			i--;
		}
		loop(i);
	}
}
