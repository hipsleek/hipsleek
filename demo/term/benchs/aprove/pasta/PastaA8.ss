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
	x>y -> requires Term[x-y] ensures true;
	x<=y -> requires Term ensures true;
}
{
	if (x > y) {
		x++;
		y = y + 2;
		loop(x, y);
	}
}
