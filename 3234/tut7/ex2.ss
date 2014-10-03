data cell {
  int val;
}

// give the strongest postcondition for
// each of the pre/post specification

int sum(cell x,cell y)
  requires x::cell<a> & x=y
  ensures x::cell<a> & res=2*a & x=y;
  requires x::cell<a> * y::cell<b>
  ensures x::cell<a> * y::cell<b> & res=a+b;
{
  int v1 = x.val;
  int v2 = y.val;
  dprint;
  return v1+v2;
}


