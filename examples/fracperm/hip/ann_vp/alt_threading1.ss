/*
  Inspired by Verifast example at
  http://people.cs.kuleuven.be/~bart.jacobs/verifast/examples/alt_threading.c.html
 */

data cell{
  int val;
}

void increment(ref cell x)
  requires x::cell<i> & @full[x]
  ensures x'::cell<i+1> & @full[x]; //'
{
  x.val++;
}

int read_int()
  requires true
  ensures true;

int delete(cell x)
  requires x::cell<i> & @value[x]
  ensures true;

int main()
  requires true
  ensures true;
{
  cell x;
  int n = read_int();
  x = new cell(n);
  int id;
  id = fork(increment,x); //only child thread has full permission of x
  dprint;
  join(id);
  int n1 = x.val;
  delete(x);
  assert n1' = n' +1;
  return 0;
}
