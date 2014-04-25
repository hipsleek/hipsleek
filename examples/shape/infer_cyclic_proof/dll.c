data node {
        int val;
        node next;
	node prev;
}


void ex41 (node y, ref node x)
// Ex 4.1
requires x::p<y>
ensures x::p<y> & x' = y;//'
{
  x = x.next;
  if (x!=y) y = y.prev;
  if (x!=y) ex41(y,x);
  dprint;
}
