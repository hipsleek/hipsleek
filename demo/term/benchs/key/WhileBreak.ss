void loop (int i)
case {
	i<=10 -> requires Term ensures true;
	i>10 -> case {
		i>=30 -> requires Loop ensures false;
		i<30 -> case {
			i>20 -> requires Term[30-i] ensures true;
			i<=20 -> requires Term[i] ensures true;
		}
	}
}
{
	if (i > 10) {
		if (i > 20) {
			i++;
		} else {
			i--;
		}
		if (i == 30) {
			return;
		}
		loop(i);
	}
}
