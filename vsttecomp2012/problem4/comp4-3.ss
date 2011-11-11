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

tlseg<p,f,d,n> ==
     self::node<d,p> & n=1 & d=f 
  or self::tlseg<r,f,d+1,n1> * r::tlseg<p,_,d+1,n2> & n=n1+n2
  inv self!=null & n>=1 & f>=d ;

// pred specifies a list of labels that would never
// be able to generate a binary tree of upto that size
// this predicate is expected to be the complement of tlseg
// which is supposed to give our completeness result

negtlseg<p,f,d,n> ==
  self::node<f,p> & n=1 & f>d
  or self::negtlseg<r,f,d+1,n> 
  or self::tlseg<r,f,d+1,n2> * r::negtlseg<p,_,d+1,n> 
  inv self!=null & n>=1 & f>d; 

/* can we show disjointness of
 (i) x::node<v,p> & v<d
 (ii) x::tsleg<p,f,d,_> 
 (iii) x::negtlseg<p,f,d,_> 
 can we show its universality? 
*/

// a provable lemma that tlseg gives at least one node
//coercion self::tlseg<p,f,d,n> -> self::node<f,q>;
//coercion self::negtlseg<p,f,d,n> -> self::node<f,q> ;

bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
{
	return x==null; 
}

int hd(node x)
    requires x::node<d,_>@I
    ensures res=d;
    requires x::tlseg<p,f,d,n>@I 
    ensures res=f;
    requires x::negtlseg<p,f,d,n>@I 
    ensures res=f;
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
// is spec below complete - how can we prove this 
 case {
   s=null -> ensures true &  flow exception;
  s!=null -> 
      requires s::node<v,_> & v<d 
      ensures  true & flow exception;
      requires s::tlseg<p,f,d,n>
      ensures res::treelseg<s,s',d,n> & s' = p & flow __norm;
      requires s::negtlseg<p,f,d,n> 
      ensures true & flow exception;
  }
{
  tree ll,rr;
  if (is_empty(s)) raise new exception();
  //unfold s;
  int h = hd(s);
  if (h < d) raise new exception();        
  if (h == d) {
      pop(s);        
	  return null;
	}
  dprint;
  ll = build_rec(d+1, s);
  //assume false;
  rr = build_rec(d+1, s);
  return new tree (ll,rr);
}

tree build(node s)
 case {
   s=null -> ensures true &  flow exception;
  s!=null ->   
      requires s::tlseg<null,_,0,n>
      ensures res::treelseg<s, null, 0, n>  & flow __norm; 
      requires s::negtlseg<p,_,0,_> 
      ensures true & flow exception ; 
}
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) raise new exception();
  else return t;
}
