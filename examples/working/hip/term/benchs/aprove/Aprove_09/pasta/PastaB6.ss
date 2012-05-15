int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();

	while (x > 0 && y > 0)
	case {
		!(x>0 & y>0) -> requires Term ensures true;
		(x>0 & y>0) -> requires Term[x] ensures true;
	}
	{
		x--;
		y--;
	}
}
