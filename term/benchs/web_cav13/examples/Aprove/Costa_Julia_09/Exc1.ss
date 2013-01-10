class NullExc extends __Exc {}

void main ()
requires Term
ensures true & flow NullExc;
{
	int i = 0;
	while (true)
	case {
		i<=10 -> requires Term[10-i] ensures true & flow NullExc;
		i>10 -> requires Term ensures true & flow NullExc;
	}
	{
		if (i > 10)
			raise new NullExc();
		i++;
	}
}
