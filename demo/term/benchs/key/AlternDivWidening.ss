void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		(-5<=i & i<=5) -> requires Term ensures true;
		!(-5<=i & i<=5) -> requires Loop ensures false;
	}
}
{
	int w = 5;
	loop_aux (i, w);
}

void loop_aux (int i, int w)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		w>=0 -> case {
			(-w<=i & i<=w) -> requires Term ensures true;
			!(-w<=i & i<=w) -> requires Loop ensures false;
		}
		w<0 -> case {
			!(w<i & -w>i) -> requires Loop ensures false;
			(w<i & -w>i) -> case {
				i=w+1 -> requires Loop ensures false;
				i!=w+1 -> case {
					i=1 -> requires Term ensures true;
					i!=1 -> requires Loop ensures false; 
				}
			}
		}
	}
}
{
	if (i != 0) {
		if (i < -w) {
			i--;
			i = -i;
		} else {
			if (i > w) {
				i++;
				i = -i;
			} else {
				i = 0;
			}
		}
		w++;
		loop_aux(i, w);
	}
}
