void main () 
{
	int x, y;
	while (x > y)
	/*
	case {
		x<=y -> requires Term ensures true;
		x>y -> case {
			x<0 -> requires Loop ensures true;
			x>=0 -> requires MayLoop ensures true;
		}
	}
	*/
	requires (x<=y & Term) or (x>y & x<0 & Loop) or (x>y & x>=0 & MayLoop)
	ensures x'<=y';
	
	{
		y = x + y;
		x = x - 1;
	}
}