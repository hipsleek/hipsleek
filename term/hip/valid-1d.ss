int foo (int x)
  requires true
  ensures res=2*x;
{
	if (x==0)
		return 0;
	else
		return 2+foo(x-1);
}

/*
TODO : Omit empty printing?
Termination checking result:
*/
