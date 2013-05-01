/*****************************************************
Example from "A discipline of programming"
Dijkstra (1976)
*****************************************************/

void loop (int x)
case {
  x=0 -> requires Term ensures true;
  x>0 -> requires Term[x] ensures true;
  x<0 -> requires Term ensures true;
}
{
  if (x!=0) {
    if (x<0)
      x = rand_int_pos();
    else
	  x = x-1;
	loop(x);
  }
}

int rand_int_pos ()
requires Term
ensures res > 0;