void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		(i>5 | i<(-5)) -> requires Loop ensures false;
		!(i>5 | i<(-5)) -> requires Term ensures true;
	}
}
{
	if (i != 0) {
		if (i > 5)
			i++;
		else {
			if (i < -5)
				i--;
			else
				i = 0;
		}
		loop(i);
	}
}
