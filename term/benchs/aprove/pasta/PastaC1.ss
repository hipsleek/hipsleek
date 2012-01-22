int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	loop_1(x);
}

void loop_1 (ref int x)
case {
	x<0 -> requires Term ensures true;
	x>=0 -> requires Term[x] ensures true;
}
{
	if (x >= 0) {
		int y = 1;
		loop_2(x, y);
		x--;
		loop_1(x);
	}
}

void loop_2 (ref int x, ref int y)
case {
	x<=y -> requires Term ensures x'=x;
	x>y -> case {
		y>0 -> requires Term[x-y] ensures x'=x;
		y<=0 -> requires Loop ensures false;
	}
}
{
	if (x > y) {
		y = 2 * y;
		loop_2(x, y);
	}
}
