void main ()
requires Loop
ensures false;
{
	int i = 0;
	while (i<20)
	case {
		i>=20 -> requires Term ensures true;
		i<20 -> requires Loop ensures false;
	}
	{
		if (i > 10) {
			//throw null;
			i = i;
		} else {
			i++;
		}
		//catch (NullPointerException e) {}
	}
}
