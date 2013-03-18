void main () 
{
	int x, y;
	while (x > y)
	
	case {
		x<=y -> requires Term ensures true;
		x>y -> case {
			x<=1 -> requires Term[1-x] ensures true;
			x>1 -> requires Term[x-y] ensures true;
		}
	}
	
	{
		y = x + y;
		x = x + 1;
	}
}
