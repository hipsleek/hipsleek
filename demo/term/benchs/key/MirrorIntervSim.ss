void loop (int i)
case {
	i=0 -> requires Term ensures true;
	i!=0 -> case {
		!(-5<=i & i<=35) -> requires Term ensures true;
		(-5<=i & i<=35) -> case {
			(0<i & i<=30) ->  requires Term[i] ensures true;
			!(0<i & i<=30) -> requires Loop ensures false;
		}
	}
}
{
	if (i != 0) {
		if (-5 <= i && i <= 35) {
			if (i < 0) {
				i = -5;
			}	else {
				if (i > 30) {
					i = 35;
				} else {
					i--;
				}
			}
		} else {
			i = 0;
		}
		loop(i);
	}
}
