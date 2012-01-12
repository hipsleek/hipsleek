// TODO: this example should result in a Loop unsoundness error?

int foo (int x)
  requires Loop
  ensures true;
{
  return foo(x);
}


int goo (int x)
  requires Loop
  ensures false;
{
	return foo(x);
}
