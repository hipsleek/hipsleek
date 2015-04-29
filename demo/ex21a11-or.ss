data cell {
  int val;
}

void pre_call(cell x)
  requires x::cell<_> ensures x::cell<3>;

bool foo2(cell x)
  requires true
  ensures res ;
{
  if (x==null) pre_call(x);

  dprint;
  return x!=null;
}

