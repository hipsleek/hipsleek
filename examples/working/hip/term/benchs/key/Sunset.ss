void loop (int i)
case {
	i<=10 -> requires Term ensures true;
	i>10 -> case {
		i<25 -> requires Term[i] ensures true;
		i>=25 -> case {
			i>30 -> requires Term ensures true;
			i<=30 -> requires Loop ensures false;
		}
	}
}
{
	if (i > 10) {
		if (i == 25) {
			i = 30;
		}
		if (i <= 30) {
			i--;
		} else {
			i = 20;
		}
		loop(i);
	}
}
