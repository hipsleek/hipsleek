int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();

	while (x > 0 && (x % 2) == 0)
	case {
		x<=0 -> requires Term ensures true;
		x>0 -> case {
			exists (m: x=2*m+1) -> requires Term ensures true;
			exists (n: x=2*n) -> requires Term ensures true;
		}
	}
	{
		x--;
	}
}
