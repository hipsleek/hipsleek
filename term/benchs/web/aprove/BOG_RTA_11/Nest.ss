int nest (int x)
case {
	x=0 -> requires Term ensures res=0;
	x>0 -> requires Term[x] ensures res=0;
	x<0 -> requires Loop ensures false;
}
{
	if (x == 0)
		return 0;
	else
		return nest(nest(x-1));
}

int rand_nat ()
requires Term
ensures res>0;

void main ()
requires Term
ensures true;
{
	int x = rand_nat();
	nest(x);
}
