//This is a good example for case inference

void complxStruc (int i)
requires MayLoop
ensures true;
{
	int j = i;
	loop(i, j);
}

void loop (int i, int j)
case {
		i<=0 -> requires Term ensures true;
		i>0 -> case {
			i=1 -> case {
				j>=(-3) & j<=1 -> requires Term ensures true;
				j<(-3) -> requires Term[-j] ensures true;
				j>1 -> requires MayLoop ensures true;
			}
			i=2 -> case {
				j<=(-1) -> requires Term[-j] ensures true;
				j>=0 -> requires MayLoop ensures true;
			}
			!(i=1 | i=2) -> requires MayLoop ensures true;
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

