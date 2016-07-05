void mirrorInterv (int i)
case {
	!(-20<=i & i<=20) -> requires Term ensures true;
	(-20<=i & i<=20) -> case {
		(i>15 | i<(-15)) -> requires Loop ensures false;
		!(i>15 | i<(-15)) -> case {
			i>0 -> requires Term ensures true;
			i<=0 -> requires Loop ensures false;
		}
	}
}
{
	int range = 20;
	loop(i, range);
}

void loop (ref int i, ref int r)
case {
	r<0 -> requires Term ensures true;
	r>=0 -> case {
		!(-r<=i & i<=r) -> requires Term ensures true;
		(-r<=i & i<=r) -> case {
			(r-i<5 | r+i<5) -> requires Loop ensures false;
			!(r-i<5 | r+i<5) -> case {
				i>0 -> requires Term[i] ensures true;
				i<=0 -> requires Loop ensures false;
			}
		}
	}
}
{
	if (-r <= i && i <= r) {
		if (r-i < 5 || r+i < 5) {
			i = -i;
		} else {
			r++;
			i--;
			if (i == 0) {
				r = -1;
			}
		}
		loop(i, r);
	}
}
