/*****************************************************
Example from "Alternation for Termination"
William R. Harris et al. (SAS'10)
*****************************************************/

bool rand_bool ()
requires Term
ensures true;

int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
  int x = rand_int();
  loop(x);
}

void loop (ref int x)
case {
  x<=0 -> requires Term ensures true;
  x>0 -> requires Term[x] ensures true;
}
{
  if (x>0) {
    if (rand_bool()) foo(x);
	else foo(x);
	loop(x);
  }
}

void foo (ref int x)
requires Term
ensures x'=x-1;
{
  x = x-1;
}