void f (int x)
requires Loop 
ensures false;
{
	if (x == 0) {
		f(1);
	} else {
		f(0);
	}
}
