void main () 
{
	int x, y;
	while (x > y)
	
	case {
		x<=y -> requires Term ensures true;
		x>y -> case {
			x<0 -> requires Loop ensures true;
			x>=0 -> case {
				4*x*x+4*x+8*y+9>=0 -> requires Term[x-y] ensures true;
				4*x*x+4*x+8*y+9<0 -> requires Loop ensures true;
			}
		}
	}
	
	{
		y = x + y;
		x = x - 1;
	}
}