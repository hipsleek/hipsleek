int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	rec(rand_int());
}

void rec (int l) 
case {
	l<=0 -> requires Term ensures true;
	l>0 -> requires Term[l] ensures true;
}
{
	if (l > 0) {
		int i = l;
		while (i < 100)
		case {
			i>=100 -> requires Term ensures l'=l;
			i<100 -> requires Term[100-i] ensures l'=l;
		}
		{
			test(i);
			i++;
		}
		rec (l - 1);
	}
}

void test(int i) 
requires Term
ensures true;
{
	descend(i);
	descend(i);
	descend(i);
	descend(i);
	descend(i);
	descend(i);
	descend(i);
	descend(i);
}

void descend (int i)
case {
	i<=0 -> requires Term ensures true;
	i>0 -> requires Term[i] ensures true;
}
{
	if (i > 0)
		descend(i - 1);
}

