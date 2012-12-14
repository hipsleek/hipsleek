void increase (int i, int j)
case {
	i+j<=0 -> requires Term ensures true;
	i+j>0 -> case {
		exists (m: j=2*m) -> requires Term[i+j] ensures true;
		exists (n: j=2*n+1) -> requires Loop ensures false;
	}
}
{
	if (i+j > 0) {
		i++;
		if (j % 2 == 0) {
			j = j - 2;
		}
		increase(i, j);
	}
}
