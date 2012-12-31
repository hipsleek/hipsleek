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

	while (x > y && x > z)
	case {
		!(x>y & x>z) -> requires Term ensures true;
		(x>y & x>z) -> requires Term[(x-y)+(x-z)] ensures true;
	}
	{
		y++;
		z++;
	}
}
