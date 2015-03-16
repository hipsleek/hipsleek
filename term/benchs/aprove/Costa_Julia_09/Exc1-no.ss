void main ()
requires Loop
ensures false;
{
	int i = 0;
	while (true)
	requires Loop ensures false;
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
