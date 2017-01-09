

data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0
	or self::node<d, r> * r::ll<n-1> & d>=0
	inv n >= 0;

bool foo(node x)
  requires x::ll<n> ensures x::ll<n>;
{
  if (x!=null){
    int d = x.val;
    dprint;
    assert x.val >= 0;
    return foo(x.next);
  }

  return true;
}
