data node {
int val;
node next;
}


ll<n> == (self = null) & (n = 0)
 or self::node<Anon_11,r> * r::ll<n2> & (n = 1+n2) & (n > 0)

inv true;
int length(node x)
requires x::ll<n> & true
ensures x::ll<n> & res = n;
{
if (x == (null)) {
  return 3;
} else {
return 1 + length(x.next);

}
}

