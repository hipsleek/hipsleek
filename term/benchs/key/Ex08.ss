void main (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Loop ensures false;
}
{
	bool up = false;
	loop(i, up);
}

void loop (int i, bool up)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Loop ensures false;
}
{
	if (i > 0) {
		if (i == 1) {
			up = true;
		}
		if (i == 10) {
			up = false;
		}
		if (up) {
			i++;
		} else {
			i--;
		}
		loop(i, up);
	}
}
