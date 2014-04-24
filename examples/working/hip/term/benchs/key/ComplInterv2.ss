void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		(-5<i & i<5) -> case {
			i<0 ->	requires Term[-i] ensures true;
			i>=0 -> requires Term[i] ensures true;
		}
		!(-5<i & i<5) -> requires Loop ensures false;
	}
}
{
	if (i != 0) {
		if (i > -5 && i < 5) {
			if (i < 0) i++;
			if (i > 0) i--;
		}
		loop(i);
	}
}
