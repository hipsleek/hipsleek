bool even (int i)
case {
	i<0 -> requires Loop ensures false;
	i>=0 -> requires Term
		case {
			exists (m: i=2*m) -> ensures res;
			exists (n: i=2*n+1) -> ensures !res;
		}
}
{
	loop(i);
	return (i == 0);
}

void loop (ref int i)
case {
	i<0 -> requires Loop ensures false;
	i>=0 -> case {
		i=0 -> requires Term ensures i'=0;
		i!=0 -> case {
			i=1 -> requires Term ensures i'=1;
			i!=1 -> case {
				exists (m: i=2*m) -> requires Term[i] ensures i'=0;
				exists (n: i=2*n+1) -> requires Term[i] ensures i'=1;
			}
		}
	}
}
{
	if (i != 1 && i != 0) {
		i = i - 2;
		loop(i);
	}
}
