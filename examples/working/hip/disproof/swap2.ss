data node {
   int val;
}

void swap(node x, node y)
requires x::node<a> * y::node<b>
ensures x::node<b> * y::node<a>;
{
  int t = x.val;
  x.val = y.val; 
  y.val = t + 7;
}
