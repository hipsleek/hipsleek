data cell {
  int val;
}

// give the strongest postcondition for
// each of the pre/post specification

int sum(cell x,cell y)
  requires x::cell<a> & x=y
  ensures true;
  requires x::cell<a> * y::cell<b>
  ensures true;
{
  int v1 = x.val;
  int v2 = y.val;
  return v1+v2;
}


