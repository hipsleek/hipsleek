hip_include 'msess/notes/node.ss'

pred ll<n> == self = null & n=0 or
  self::node<_,q> * q::ll<n-1>;


int length(node x)
  requires x::ll<n>
  ensures  x::ll<n> & res =n;
{
  if(x==null) return 0;
  else return 1+length(x.next);
}

void main(node x, node y)
  requires x::ll<m> * y::ll<mm>
  ensures  x::ll<m> * y::ll<mm>;
{
  int xx = length(x);
  int yy = length(y);
  dprint;
}
