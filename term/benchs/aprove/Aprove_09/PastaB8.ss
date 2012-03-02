int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();

	if (x > 0) {
		while (x != 0)
		case {
			x=0 -> requires Term ensures true;
			x!=0 -> case {
				x>0 -> requires Term[x] ensures true;
				x<=0 -> requires Loop ensures false;
			}
		}
		{
			if (x % 2 == 0) {
				x = x/2;
			} else {
				x--;
			}
		}
	}
}
