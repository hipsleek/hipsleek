data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

class exception extends __Exc {}

  
tlseg<p,d,n> ==
     self::node<d,p> & n=1 
  or self::tlseg<r,d+1,n1> * r::tlseg<p,d+1,n2> & n=n1+n2 
  inv self!=null & n>=1;
  
negtlseg<p,d,n> ==
     self=null & n=0
  or self::node<v,p> & n=1 & v!=d
  or self::negtlseg<r,d+1,n1> * r::tlseg<p,d+1,n2> & n=n1+n2
  or self::tlseg<r,d+1,n1> * r::negtlseg<p,d+1,n2> & n=n1+n2
  or self::negtlseg<r,d+1,n1> * r::negtlseg<p,d+1,n2> & n=n1+n2
  inv n>=0; 
  
lemma self::negtlseg<p,d,n> & n>0 -> self::node<dd,q>;

bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
{
	return x==null; 
}

int hd(node x)
    requires x::node<d,_>@I
    ensures res=d;
    requires x::negtlseg<_,d,n>@I & n>0
    ensures true;
{
  return x.val;
}

void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  
{
	x = x.next;
}

tree build_rec (int d, ref node s)
  requires s::negtlseg<p,d,n>  ensures true & flow exception;
{
  tree ll,rr;
	if (is_empty(s)) raise new exception();
  int h = hd(s);
  if (h < d) raise new exception();        
  if (h == d) {
      pop(s);        
			return null;
	}    
  ll = build_rec(d+1, s);
  rr = build_rec(d+1, s);
	return new tree (ll,rr);
}

tree build(node s)
  requires s::negtlseg<p,d,n> ensures true & flow exception ; 
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) raise new exception();
  else return t;
}
