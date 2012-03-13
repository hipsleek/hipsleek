/*****************************************************
Example from "Alternation for Termination"
William R. Harris et al. (SAS'10)
*****************************************************/

bool rand_bool ()
requires Term
ensures true;

void foo ()
requires MayLoop
ensures true;
{
  int d = 1;
  int x;
  if (rand_bool()) d = d-1;
  if (rand_bool()) foo();
  if (rand_bool()) foo();
  if (rand_bool()) d = d-1;
  loop(x, d);
}

void loop (ref int x, ref int d)
case {
  x<=0 -> requires Term ensures true;
  x>0 -> case {
    d<=0 -> requires Loop ensures false;
	d>0 -> requires Term[x] ensures true;
  }
}
{
  if (x>0) {
   x = x-d;
   loop(x, d);
  }
}