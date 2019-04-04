data node {
	node next;
}

ll<n> == self = null & n = 0
	or self::node<q> * q::ll<n-1>
  inv n >= 0;

node delete_last(node x)
requires x::ll<n> & n <= 1
ensures emp & res = null;
requires x::ll<n> & n > 1
ensures x::ll<n-1> & res = x;
{
  if (x == null) return null;
  if (x.next == null) {
     free(x);
     return null;
  }
  if (x.next.next == null){
     free(x.next);
     // dprint;
     // x.next = null;
  }
  else delete_last(x.next);
  return x;
}