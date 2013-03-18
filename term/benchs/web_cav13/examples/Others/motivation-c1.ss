void main () 
requires MayLoop
ensures true;
{
	int x, y;
	while (x > y)
	
	case {
		x<=y -> requires Term ensures true;
		x>y -> case {
			x<0 -> requires Loop ensures true;
			x>=0 -> requires MayLoop ensures true;
		}
	}
	
	
	{
		y = x + y;
		x = x - 1;
	}
}
