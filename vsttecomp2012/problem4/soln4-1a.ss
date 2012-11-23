data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

class exception extends __Exc {}

// pred specifies that t is is linked-list of ints
// is a correct labelling for binary tree from self
//   where tree<left,right> is binary node
//         null is leaf of tree
treelseg<t,p,d,n> ==
     t::node<d,p> & self=null & n=1
  or self::tree<left,right> * left::treelseg<t,r,d+1,n1> 
     * right::treelseg<r,p,d+1,n2> & n=n1+n2
  inv n>=1 ;

// pred that describe a link list segment of integers that
// would build a binary tree of size n according the label
tlseg<p,d,n> ==
     self::node<d,p> & n=1 
  or self::tlseg<r,d+1,n1> * r::tlseg<p,d+1,n2> & n=n1+n2 
  inv self!=null & n>=1;

// a provable lemma that tlseg gives at least one node
lemma self::tlseg<p,d,n> -> self::node<dd,q> & dd>=d;
 
bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
{
	return x==null; 
}

int hd(node x)
    requires x::node<d,_>@I
    ensures res=d;
    requires x::tlseg<_,d,n>@I & n>1
    ensures res>=d;
{
  return x.val;
}

void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  //'
{
	x = x.next;
}

// below captures the soundness of build_rec
// the input list of labels according to tlseg
// will always produce a binary tree in accordance
// with the label (captured by treelseg) without
// encountering any exceptions and returning s'=p
tree build_rec (int d, ref node s)
 requires s::tlseg<p,d,n>@I
 ensures res::treelseg<s,s',d,n>@I & s' = p & flow __norm;
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

// below captures the soundness of build
// the input list s of length n according to tlseg
// will always produce a binary tree according to
// treelseg without encountering any exception
tree build(node s)
  requires s::tlseg<null,0,n>@I
  ensures res::treelseg<s, null, 0, n>@I  & flow __norm; 
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) raise new exception();
	else return t;
}

/*
tree harness1(node s1)
	requires s1::node<1,s2>*s2::node<3,s3>
      *s3::node<3,s4>*s4::node<2,null>
  ensures res::treelseg<s1,null,0,4>;
{
	return build(s1);
}*/
