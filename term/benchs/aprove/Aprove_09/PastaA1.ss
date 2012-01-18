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
	x<=0 -> requires Term ensures true;
	x>0 -> requires Term[x] ensures true;
}
{
	if (x > 0) {
		int y = 0;
		loop_2(x, y);
		x--;
		loop_1(x);
	}
}

void loop_2 (ref int x, ref int y)
case {
	y>=x -> requires Term ensures x'=x;
	y<x -> requires Term[x-y] ensures x'=x;
}
{
	if (y < x) {
		y++;
		loop_2(x, y);
	}
}
