void increase (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> case {
		i>3 -> requires Loop ensures false;
		i<=3 -> requires Term[i] ensures true;
	}
}
{
	if (i > 0) {
		if (i > 3) {
			i++;
		} else {
			i--;
		}
		increase(i);
	}
}
