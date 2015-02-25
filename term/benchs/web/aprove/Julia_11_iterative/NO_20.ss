void main ()
requires Loop
ensures false;
{
	while (true) 
	requires Loop ensures false;
	{ int i = 0; }
}
