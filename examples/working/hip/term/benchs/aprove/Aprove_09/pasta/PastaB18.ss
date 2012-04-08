int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	
	loop(x, y);
}

void loop (ref int x, ref int y)
case {
	!(x>0 & y>0) -> requires Term ensures true;
	(x>0 & y>0) -> requires Term ensures true;
}
{
	if (x > 0 && y > 0) {
		if (x > y) {
			decrease(x);
		} else {
			decrease(y);
		}
		loop(x, y);
	}
}

void decrease (ref int x)
case {
	x<=0 -> requires Term ensures x'=x;
	x>0 -> requires Term[x] ensures x'=0;
}
{
	if (x > 0) {
		x--;
		decrease(x);
	}
}

