int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int i = rand_int();
	
	while (i >= 0) 
	case {
		i<0 -> requires Term ensures true;
		i>=0 -> requires Term[i] ensures true;
	}
	{
		int j = 0;
		while (i >= j + 1)
		case {
			i<j+1 -> requires Term ensures i'=i;
			i>=j+1 -> requires Term[i-j] ensures i'=i;
		}
		{
			j++;
		}
		i--;
	}
}
