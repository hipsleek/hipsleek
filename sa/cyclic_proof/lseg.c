data node {
        int val;
        node next;
}

// shape only
ls<p> == self=p
        or self::node<_, q> * q::ls<p>
        inv true;

// shape and size
lseg<p, n> == self=p & n=0
        or self::node<_, q> * q::lseg<p, n-1>
        inv n>=0;
//infer
p<y> == self::node<_,y>
	or self::node<_,t> * t::p<y> & t != y
	inv true;

void ex41 (node y, ref node x)
// Ex 4.1
requires x::p<y>
ensures x::p<y> & x' = y;//'
{
  x = x.next;
  if (x!=y) ex41(y,x);
  dprint;
}
