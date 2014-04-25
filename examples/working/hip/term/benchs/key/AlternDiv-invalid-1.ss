void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		i=1 -> requires Term ensures true;
		i!=1 -> requires Loop ensures false;
	}
}
{
	if (i != 0) {
		if (i < 0) {
			i--;
			i = i * (-1);
		} else {
			i--;
			i = i * (-1);
		}
		loop(i);
	}
}
