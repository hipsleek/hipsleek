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
  inv n>=0;

lseg<p,n,mx> == self=p & n=0 & mx=0
  or self::node<v,r> * r::lseg<p,n-1,mx1> & mx=max(mx1,v) & v>0 
  inv n>=0 & mx>=0;


bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
  requires x::lseg<pp,n,_>
  case {
    x=null -> ensures res;
    x!=null -> ensures !res;
  }
  /*
  case {
    x=null -> ensures res;
    x!=null -> ensures !res;
  }
  */
{
	return x==null; 
}

int hd(node x)
 case {
  x=null -> ensures true & flow exception;
  x!=null ->  
    requires x::node<i,_>@I 
    ensures res=i;
 }
{
  if (x==null) raise new exception();
  else return x.val;
}

void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  //' removes a node
{
	x = x.next;
}

//lemma "lsegbrk" self::lseg<p,n> & n=a+b & a>0 & b>0 & n>=2 -> self::lseg<q,a> * q::lseg<p,b>;

tree build_rec (int d, ref node s)
 requires s::lseg<null,n,mx>
 variance (1) [mx-d]
 case {
  n=0 -> ensures true & flow exception;
  n!=0 -> ensures  res::treelseg<s, pp, d, m> 
                         * pp::lseg<null,n-m,mx1> & s'=pp & mx1 <= mx & flow __norm //'
                   or true & flow exception ; 
  }
{
    tree ll,rr;
    exception ve;
    ve = new exception();
	if (s == null) raise ve;
	int h = hd(s);
	if (h < d) raise ve;
    if (h == d) {
		pop(s);   
		return null;
	}    
	ll = build_rec(d+1, s);
 	rr = build_rec(d+1, s);
	return new tree (ll,rr);
}


tree build(node s)
  requires s::lseg<null,n,_>
  ensures res::treelseg<s, null, 0, n>@I & flow __norm
      or true & flow exception ; 
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) {
		raise new exception();
	} else {
		return t;
	}
}

