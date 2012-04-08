class NullExc extends __Exc {}

void main ()
requires Loop
ensures false;
{
	int i = 0;
	while (true)
	requires Loop ensures false & flow NullExc;
	{
		if (i > 10)
			raise new NullExc();
		i++;
	}
}
