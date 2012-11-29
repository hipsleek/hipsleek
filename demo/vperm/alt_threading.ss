/*
  Inspired by Verifast example at
  http://people.cs.kuleuven.be/~bart.jacobs/verifast/examples/alt_threading.c.html

  Description: This program demonstrates the passing of
  variable permissions from a parent thread to a child thread. We use a variable instead of a heap cell.

 */

void increment(ref int x)
  requires true //@full[x]
  ensures x'=x+1; // & @full[x]; //'
{
  x++;
}

int read_int()
  requires true
  ensures true;

int main()
  requires true
  ensures true;
{
  int x;
  int n;
  n = read_int();
  x=n;
  int id;
  id = fork(increment,x); //only child thread has full permission of x
  join(id);
  int n1 = x;
  assert n1' = n' +1;
  return 0;
}
