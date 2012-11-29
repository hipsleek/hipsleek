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

	while (x > y + z)
	case {
		x<=y+z -> requires Term ensures true;
		x>y+z -> requires Term[x-y-z] ensures true;
	}
	{
		y++;
		z++;
	}
}
