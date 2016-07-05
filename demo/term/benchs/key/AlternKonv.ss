void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		exists(m: i=2*m) -> case {
			i<=0 -> requires Term[-i] ensures true;
			i>0 -> requires Term[i] ensures true;
		}
		exists(n: i=2*n+1) -> requires Loop ensures false;
	}
}
{
	if (i != 0) {
		if (i < 0) {
			i = i + 2;
			if (i < 0) {
				i = -i;
			}
		} else {
			i = i - 2;
			if (i > 0) {
				i = -i;
			}
		}
		loop (i);
	}
}
