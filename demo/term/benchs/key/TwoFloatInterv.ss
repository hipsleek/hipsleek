void loop (int i)
case {
	!(0 < i & i < 50) -> requires Term ensures true;
	(0 < i & i < 50) -> case {
		i<=11 -> requires Term[i] ensures true;
		i>11 -> case {
			i<40 -> requires Loop ensures false; 
			i>=40 -> requires Term[50-i] ensures true;
		}
	}
}
{
	if (0 < i && i < 50) {
		if (i < 20) {
			i--;
		}
		if (i > 10) {
			i++;
		}
		if (30 <= i && i <= 40) {
			i--;
		}
		loop(i);
	}
}
