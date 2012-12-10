void up (int n)
case {
	n>=15 -> requires Term ensures true;
	n<15 -> requires Loop ensures false;
}
{
	int d = 10;
	loop(n, d);
}

void loop (ref int n, ref int d)
requires d>0
case {
	n>=15 -> requires Term ensures true;
	n<15 -> case {
		d<=15 -> requires Loop ensures false;
		d>15 -> requires Term[15-n] ensures true;
	}
}
{
	if (n < 15) {
		n++;
		n = n % d;
		loop(n, d);
	}
}
