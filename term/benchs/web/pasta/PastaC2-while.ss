int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	
	while (x >= 0)
	case {
		x<0 -> requires Term ensures true;
		x>=0 -> requires Term[x] ensures true;
	}
	{
		x = x + 1;
		int y = 1;
		
		while (x >= y)
		case {
			x<y -> requires Term ensures x'=x;
			x>=y -> requires Term[x-y] ensures x'=x;
		}
		{
			y++;
		}
		x = x - 2;
	}
}
