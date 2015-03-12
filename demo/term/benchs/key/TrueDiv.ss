void loop (int i)
requires Loop 
ensures false;
{
	if (true) {
		if (i <= 0) 
			i--;
		else
			i++;
		loop(i);
	}
}
