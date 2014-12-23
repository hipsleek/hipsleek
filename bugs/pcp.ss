
void loop (ref int i, ref int j)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> case {
		i>=j -> requires Term ensures true;
		i<j -> requires Term[j-i] ensures true;
	}
}
{
	if (i > 0) {
		if (i >= j) {
			return;
			//skip ();
		} else { // i < j
			if (i > 0 && j < 0) { // unreachable 
				i--;
				if (j < -1) {
					j++;
				} else {
					i++;
				}
			} else {
				i++;
				if (j*2 > i) {
					j--;
				} else {
					j++;
				}
			}
		}
		loop(i, j);
	}
}

void skip () 
requires Term
ensures true;
