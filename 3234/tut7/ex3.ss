data cell {
  int val;
}

// why did verification below succeed?
// each of the pre/post specification

int sum(cell x,cell y)
  requires x::cell<_>*x::cell<_> 
  ensures false;
{
  int v1 = x.val;
  int v2 = y.val;
  return v1+v2;
}


