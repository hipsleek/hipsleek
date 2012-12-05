int half (int x)
requires Term
case {
	x<=1 -> ensures res=0;
	x>1 -> case { 
		exists (k1: x=2*k1) -> ensures x=2*res;
		exists (k2: x=2*k2+1) -> ensures x=2*res+1;
	}
}
{
	int r = 0;
	while (x > 1)
	case {
		x<=1 -> requires Term ensures x'=x & r'=r;
		x>1 -> requires Term[x] ensures x=x'+2*(r'-r) & (x'=0 | x'=1);
	}
	{
		x = x - 2;
		r++;
	}

	return r;
}

int log (int x)
requires Term
ensures true;
{
	int r = 0;
	
	while (x > 1)
	case {
		x<=1 -> requires Term ensures true;
		x>1 -> requires Term[x] ensures true;
	}
	{
		x = half(x);
		r++;
	}

	return r;
}

int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	log(x);
}
