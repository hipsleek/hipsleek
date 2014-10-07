//This is a good example for case inference

void complxStruc (int i)
requires Term
ensures true;
{
	int j = i;
	loop(i, j);
}

void loop (ref int i, ref int j)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires j>=0 
	case {
		i<j -> requires Term ensures true;
		i>=j -> requires Term[i-j, j] ensures true;
	}
}
{
	if (i > 0) {
		if (i >= j) {
			i--;
			if (j < 5) {
				j++;
				if (i-j > 2) {
					i++;
				} else {
					j++;
				}
			} else {
				j--;
			}
		} else { // i < j
			return;
		}
		loop(i, j);
	}
}
