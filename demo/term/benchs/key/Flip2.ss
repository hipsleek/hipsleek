void flip (int i, int j)
case {
	!(i>0 & j>0) -> requires Term ensures true;
	(i>0 & j>0) -> case {
		i=1 -> case {
			j=1 -> requires Term ensures true;
			j!=1 -> requires Loop ensures false;
		}
		i!=1 -> requires Loop ensures false;
	}
}
{
	if (i > 0 && j > 0) {
		if (i < j) {
			int t = i;
			i = j;
			j = t;
		} else {
			if (i > j) {
				j = i;
			} else {
				i--;
			}
		}
		flip(i, j);
	}
}
