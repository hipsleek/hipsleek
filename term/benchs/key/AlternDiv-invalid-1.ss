void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> requires Term[i] ensures true;
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
