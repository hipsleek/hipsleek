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

/*
tlseg<p,f,d,n> ==
     self::node<d,p> & n=1 & d=f 
  or self::tlseg<r,f,d+1,n1> * r::tlseg<p,_,d+1,n2> & n=n1+n2
  inv self!=null & n>=1 & f>=d ;
*/

// with tlseg unfolded twice
tlseg<p,f,d,n> ==
     case {
     d=f -> [] self::node<d,p> & n=1;
     d!=f -> 
        case {
          f=d+1 -> [] self::node<d+1,r> * r::tlseg<p,_,d+1,n2> & n=1+n2;
          f!=d+1 -> 
          case {
          f=d+2 -> [] self::node<d+2,r1> * r1::tlseg<r,_,d+2,n1> * r::tlseg<p,_,d+1,n2> & n=1+n1+n2;
          f!=d+2 -> [] self::tlseg<r,f,d+1,n1> * r::tlseg<p,_,d+1,n2> & n=n1+n2;
          };
       };
     }
inv self!=null & n>=1 & f>=d;

 
// pred specifies a list of labels that would never
// be able to generate a binary tree of upto that size
// this predicate is expected to be the complement of tlseg
// which is supposed to give our completeness result

// with negtlseg unfolded twice

/*
negtlseg<p,f,d,n> ==
  self::node<f,p> & n=1 & f<d
  or self::negtlseg<p,f,d+1,n> & f!=d 
  or self::tlseg<r,f,d+1,n1> * r::negtlseg<p,_,d+1,n2> & n=n1+n2
inv self!=null & n>=1 & f!=d; 
*/

negtlseg<p,f,d,n> ==
 case {
  f<d -> [] self::node<f,p> & n=1 & f<d;
  f>=d -> 
 case {
    f=d+1 -> [] self::node<f,r> * r::negtlseg<p,_,d+1,n2> & n=1+n2;
    f!=d+1 -> 
  case {
      f=d+2 ->
       [] self::node<f,r> * r::negtlseg<p,_,d+2,n2> & n=1+n2 
       or self::node<f,r1>*r1::tlseg<r,f,d+2,n1> * r::negtlseg<p,_,d+1,n2> & n=1+n1+n2;
  f!=d+2 ->
        [] self::negtlseg<p,f,d+1,n> & f!=d 
       or self::tlseg<r,f,d+1,n1> * r::negtlseg<p,_,d+1,n2> & n=n1+n2;
    };
  };
  }
  inv self!=null & n>=1 & f!=d; 



/*

negtlseg<p,f,d,n> ==
 case {
  f<d -> [] self::node<f,p> & n=1 & f<d;
  f>=d -> []
        self::negtlseg<p,f,d+1,n> & f!=d 
     or self::tlseg<r,f,d+1,n1> * r::negtlseg<p,_,d+1,n2> & n=n1+n2;
  }
  inv self!=null & n>=1 & f!=d; negtlseg<p,f,d,n> ==
 case {
  f<d -> [] self::node<f,p> & n=1 & f<d;
  f>=d -> []
        self::negtlseg<p,f,d+1,n> & f!=d 
     or self::tlseg<r,f,d+1,n1> * r::negtlseg<p,_,d+1,n2> & n=n1+n2;
  }
  inv self!=null & n>=1 & f!=d; 


negtlseg<p,f,d,n> ==
 case {
  f<d -> [] self::node<f,p> & n=1 & f<d;
  f=d -> [] false;
  f>d -> [] self::negtlseg<p,f,d+1,n> & f!=d 
     or self::tlseg<r,f,d+1,n1> * r::negtlseg<p,_,d+1,n2> & n=n1+n2;
  }
  inv self!=null & n>=1 & f!=d; 
*/

/* can we show disjointness of
 (i) x=null
 (ii) x::tsleg<p,f,d,_> 
 (iii) x::negtlseg<p,f,d,_> 
 can we show its universality?, namely
 true |- (i) \/ (ii) \/ (iii)
*/

// a provable lemma that tlseg gives at least one node
//lemma self::tlseg<p,f,d,n>@I -> self::node<f,q>@I;
//lemma self::negtlseg<p,f,d,n>@I -> self::node<f,q>@I ;

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
/*
// can be proven with the lemma
{
  return x.val;
}
*/
void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  //'

tree build_rec (int d, ref node s)
// is spec below complete - how can we prove this 
 case {
  s=null -> ensures true &  flow exception;
  s!=null -> 
      requires s::tlseg<p,f,d,n>
      ensures  res::treelseg<s,s',d,n> & s' = p & flow __norm;
      requires s::negtlseg<_,_,d,_> 
      ensures  true & flow exception;
  }
{
  tree ll,rr;
  if (is_empty(s)) raise new exception();
  int h = hd(s);
  if (h < d) raise new exception();        
  unfold s;
  if (h == d) {
      pop(s);        
	  return null;
	}
  ll = build_rec(d+1, s);
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


tree harness1(node s1)
  requires s1::node<1,s2>*s2::node<3,s3>*s3::node<3,s4>*s4::node<2,null>
  ensures res::treelseg<s1,null,0,4>;
{
	return build(s1);
}

tree harness2(node s1)
  requires s1::node<1,s2>*s2::node<3,s3>*s3::node<2,s4>*s4::node<2,null>
  ensures true & flow exception;
{
	return build(s1);
}
