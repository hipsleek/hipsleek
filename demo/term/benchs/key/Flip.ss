void flip (int i, int j)
case {
	!(i!=0 & j!=0) -> requires Term ensures true;
	(i!=0 & j!=0) -> requires Loop ensures false;
}
{
	if (i != 0 && j != 0) {
		int t = i;
		i = j;
		j = t;
		flip(i, j);
	}
}
