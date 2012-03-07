void loop (int i)
case {
	i<=2 -> requires Term ensures true;
	i>2 -> requires Loop ensures false;
}
{
	if (i > 2) 
		loop(i + 1);
}
