class NullExc extends __Exc {}

void main ()
requires Loop
ensures false;
{
	int i = 0;
	loop(i);
}

void loop (ref int i)
case {
	i>=20 -> requires Term ensures true;
	i<20 -> requires Loop ensures false;
}
{
	if (i < 20) {
		i--;

		try {
			if (i > 10) {
				//throw null;
				raise new NullExc ();
				i++;
			}
			else
				i = i + 2;
		}
		catch (NullExc e) {
			i++;
		};;
		loop(i);
	}
}
