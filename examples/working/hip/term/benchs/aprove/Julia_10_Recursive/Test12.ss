int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{

	int x = rand_int();
	int y = rand_int();
	rec(x, y);
}

void rec (int x, int y) 
case {
	x+y<=0 -> requires Term ensures true;
	x+y>0 -> requires Term[x+y] ensures true;
}
{
	if (x + y > 0) {
		int a = rand_int();
		int b = rand_int();
		if (a * b > 9)
			rec(x - 1, y);
	  else
			rec(x, y - 1);
	}
}

