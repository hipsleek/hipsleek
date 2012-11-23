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
	i<20 -> case {
		i<=10 -> requires Loop ensures false;
		i>10 -> requires Term[20-i] ensures true;
	}
}
{
	if (i < 20) {
		if (i <= 10) 
			//continue;
			i = i;
		else
			i++;
		loop(i);
	}
}
