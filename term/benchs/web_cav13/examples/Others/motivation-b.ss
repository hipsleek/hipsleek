void main () 
{
	int x, y;
	while (x > y)
	/*
	case {
		x<=y -> requires Term ensures true;
		x>y -> case {
			x<=1 -> requires Term[1-x] ensures true;
			x>1 -> requires Term[x-y] ensures true;
		}
	}
	*/
	requires (x<=y & Term) or (x>y & x<=1 & Term[1-x]) or (x>y & x>1 & Term[x-y])
	ensures true;
	{
		y = x + y;
		x = x + 1;
	}
}