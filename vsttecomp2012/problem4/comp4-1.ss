data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

class exception extends __Exc {}

treelseg<t,p,d,n> ==
     t::node<d,p> & self=null & n=1
  or self::tree<left,right> * left::treelseg<t,r,d+1,n1> 
     * right::treelseg<r,p,d+1,n2> & n=n1+n2
  inv n>=1 ;
  
tlseg<p,d,n> ==
     self::node<d,p> & n=1 
  or self::tlseg<r,d+1,n1> * r::tlseg<p,d+1,n2> & n=n1+n2 
  inv self!=null & n>=1;

coercion self::tlseg<p,d,n> -> self::node<dd,q> & dd>=d;
 

bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
{
	return x==null; 
}

int hd(node x)
    requires x::node<d,_>@I
    ensures res=d;
    requires x::tlseg<_,d,n>@I
    ensures res>=d;
{
  return x.val;
}

void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  //' removes a node
{
	x = x.next;
}

tree build_rec (int d, ref node s)
 requires s::tlseg<p,d,n> 
 ensures res::treelseg<s,s',d,1> & s' = p & flow __norm;
{
  tree ll,rr;
	if (is_empty(s)) raise new exception();
  int h = hd(s);
  if (h < d) raise new exception();        
  if (h == d) {
      pop(s);        
        
			return null;
	}    
  assert h'=d';// assume h'>d';
  ll = build_rec(d+1, s);
  rr = build_rec(d+1, s);
	return new tree (ll,rr);
}


tree build(node s)
  requires s::tlseg<p,d,n>
  ensures res::treelseg<s, null, 0, n>@I & flow __norm; 
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) {
		raise new exception();
	} else {
		return t;
	}
}