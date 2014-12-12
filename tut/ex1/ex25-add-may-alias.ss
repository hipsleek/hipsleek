// run with --imm option for spatial-&

data cell {
  int val;
}

int add_pair(cell x, cell y)
  requires x::cell<a> * y::cell<b>
  ensures  x::cell<a> * y::cell<b> & res=a+b;
  requires x::cell<a> & x=y
  ensures  x::cell<a> & res=a+a;
{
  return x.val + y.val;
}

int add_pair2(cell x, cell y)
  requires (x::cell<a>@L & y::cell<b>@L)
  ensures  res=a+b;
{
  return x.val + y.val;
}

int main(cell x,cell y)
  requires x::cell<2>@L * y::cell<3>@L
  ensures res=4+5;
{
  int t = add_pair2(x,x);
  return t+add_pair2(x,y);
}
