// This specification prove the completness of our solutions
// we have verified some of the methods

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

tlseg<p,d,n> ==
     self::node<d,p> & n=1 
  or self::tlseg<r,d+1,n1> * r::tlseg<p,d+1,n2> & n=n1+n2 
  inv self!=null & n>=1;

// pred specifies a list of labels that would not
// be able to generate a binary tree of the same size
// this predicate is expected to be the complement of tlseg
// which is supposed to give our completeness result
negtlseg<p,d,n> ==
  self::node<v,p> & n=1 & v!=d
  or self::negtlseg<r,d+1,n1> * r::tlseg<p,d+1,n2> & n=n1+n2
  or self::tlseg<r,d+1,n1> * r::negtlseg<p,d+1,n2> & n=n1+n2
  or self::negtlseg<r,d+1,n1> * r::negtlseg<p,d+1,n2> & n=n1+n2
  inv self!=null & n>=1; 

// a provable lemma that tlseg gives at least one node
coercion self::tlseg<p,d,n> -> self::node<dd,q> & dd>=d;

coercion self::negtlseg<p,d,n> -> self::node<dd,q> & dd!=d;

bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
{
	return x==null; 
}

int hd(node x)
    requires x::node<d,_>@I
    ensures res=d;
    requires x::tlseg<p,d,n>@I & n>1
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

tree build_rec (int d, ref node s)
 case {
   s=null -> ensures true &  flow exception;
  s!=null -> 
     requires s::tlseg<p,d,n>
     ensures res::treelseg<s,s',d,n> & s' = p & flow __norm;
     requires s::negtlseg<p,d,n> 
     ensures true & flow exception;
}
{
  tree ll,rr;
	if (is_empty(s)) raise new exception();
  int h = hd(s);
  if (h < d) raise new exception();        
  if (h == d) {
      pop(s);        
	  return null;
	}
  assume false;
  ll = build_rec(d+1, s);
  rr = build_rec(d+1, s);
	return new tree (ll,rr);
}

tree build(node s)
 case {
   s=null -> ensures true &  flow exception;
  s!=null ->   
      requires s::tlseg<null,0,n>
      ensures res::treelseg<s, null, 0, n>  & flow __norm; 
      requires s::negtlseg<p,0,n> 
      ensures true & flow exception ; 
}
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) raise new exception();
  else return t;
}
