void main ()
requires MayLoop
ensures true;
{
	int x = length();
	loop(x);
}

void loop (ref int x)
case {
	x<=0 -> requires Term ensures x'=x;
	x>0 -> requires Loop ensures false;
}
{
	if (x > 0) {
		f(x);
		x = x + 1;
		loop(x);
	}
}

void f (ref int x)
case {
	x<=0 -> requires Term ensures x'=x;
	x>0 -> requires Term[x] ensures x'=0;
}
{
	if (x > 0) {
		x = x - 1;
		f(x);
	}
	return;
}

int length () 
requires Term
ensures res>=0;
