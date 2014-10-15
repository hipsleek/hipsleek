void flip (int i, int j)
case {
	!(i>0 & j>0) -> requires Term ensures true;
	(i>0 & j>0) -> requires Term[i+j, j] ensures true;
}
{
	if (i > 0 && j > 0) {
		if (i < j) {
			int t = i;
			i = j;
			j = t;
		} else {
			if (i > j) {
				i = j;
			} else {
				i--;
			}
		}
		flip(i, j);
	}
}
