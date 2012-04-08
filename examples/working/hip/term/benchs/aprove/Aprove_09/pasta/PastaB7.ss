int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int z = rand_int();

	while (x > z && y > z)
	case {
		!(x>z & y>z) -> requires Term ensures true;
		(x>z & y>z) -> requires Term[x-z] ensures true;
	}
	{
		x--;
		y--;
	}
}
