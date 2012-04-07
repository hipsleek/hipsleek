/*
The program does not terminate when the inputs are float.
*/
void plait (int i, int j, int k)
requires i>=0 & j>=0 & k>=0
ensures true;
{
	int plaitNext = 0;
	int swap = 0;

	while (i > 0 || j > 0 || k > 0)
	requires i>=0 & j>=0 & k>=0 & plaitNext >=0 & plaitNext<=1
	case {
		(i>0 | j>0 | k>0) -> case {
			(exists (k0: k=4*k0)) -> case {
				exists (j0: j=2*j0) -> requires Loop ensures false;
				exists (j1: j=2*j1+1) -> case {
					plaitNext=0 -> case {
						k=0 -> requires Term ensures true;
						k!=0 -> requires Loop ensures false;
					}
					plaitNext!=0 -> requires MayLoop ensures true;
				}
			}
			!((exists (k1: k=4*k1))) -> requires MayLoop ensures true;
		}
		!(i>0 | j>0 | k>0) -> requires Term ensures true;
	}
	{
		if (plaitNext == 0) {
			//assume (exists j2: j=2*j2+1);
			swap = i;
			i = j/2;
			//i = div2(j);
			j = swap*2;
			plaitNext = 1;
			//dprint;
		} else {
			swap = k;
			k = j*2;
			j = swap/2;
			//j = div2(swap);
			plaitNext = 0;
		}
	}
}

int div2 (int x)
requires x>=0 & Term
case {
	exists (x0: x=2*x0) -> ensures x=2*res;
	exists (x1: x=2*x1+1) -> ensures x=2*res+1;
}
