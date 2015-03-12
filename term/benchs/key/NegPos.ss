void loop (int i, int j)
case {
	i>0 -> case {
		j>0 -> requires Term[i] ensures true;
		j<=0 -> requires Term ensures true;
	}
	i=0 -> requires Term ensures true;
	i<0 -> case {
		j>=0 -> requires Term ensures true;
		j<0 -> requires Term[-j] ensures true;
	}
}
{
	if (i*j > 0) {
		i--;
		j++;
		loop(i, j);
	}
}
