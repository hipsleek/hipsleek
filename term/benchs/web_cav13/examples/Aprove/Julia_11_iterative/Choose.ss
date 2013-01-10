void main ()
requires Loop 
ensures false;
{
	int i = 3;
	loop(i);
}

void loop (ref int i)
case {
	i<3 -> requires Term ensures true;
	i>=3 -> requires Loop ensures false;
}
{
	if (i >= 3) {
		if (i > 5)
			i = i + 3;
		else if (i > 10)
			i = i - 2;
		else
			i++;
		loop(i);
	}
}
