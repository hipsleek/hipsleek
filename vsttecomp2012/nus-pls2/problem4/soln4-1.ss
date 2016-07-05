/*
  This spec prove the soundness of build function.
  
*/

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

// pred for a linked list of int of length n
ll<n> == self=null & n=0
  or self::node<v, r> * r::ll<n-1> 
  inv n>=0;


bool is_empty(node x)
  requires true
  ensures true & (x=null & res | x!=null & !res);
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

// below captures the soundness of build_rec
// the input list s of length n is immutable
// the postcondition says that either 
//   (i) there is an exception, or 
//   (ii) if it returns normally, it produces
//        a binary tree of size m according to s
//        the residue list is captured by s 
tree build_rec (int d, ref node s)
 requires s::ll<n>@I
 case {
  n=0 -> ensures true & flow exception;
  n!=0 -> ensures  res::treelseg<s, pp, d, m>@I 
                      * pp::ll<n-m>@I & s'=pp & flow __norm //'
                 or true & flow exception ; 
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
	ll = build_rec(d+1, s);
 	rr = build_rec(d+1, s);
	return new tree (ll,rr);
}


// below captures the soundness of build
// the input list s of length n is immutable
// the postcondition says that either 
//   (i) there is an exception, or 
//   (ii) if it returns normally, it produces
//        a binary tree of size n according to s
tree build(node s)
  requires s::ll<n>@I
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

/*
tree harness1(node s1)
	requires s1::node<1,s2>@I*s2::node<3,s3>@I
      *s3::node<3,s4>@I*s4::node<2,null>@I 
  ensures res::treelseg<s1,null,0,4>@I 
        or true & flow exception;
{
	return build(s1);
}
*/
