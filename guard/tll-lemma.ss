// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<_,null,lr> & self = ll
  or self::node<l,r,_> * l::tll<ll,z> * r::tll<z,lr> //& r!=null
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<_,null,_>
	or self::node<l,r,_> * l::tree<> * r::tree<>
	inv self!=null;

 GG<rr,t> == self::node<DP1,right,t> & right=null & rr=self
   or self::node<left,right,DP> * left::GG<rr,l> 
         * right::GG<l,t> & right!=null
   inv true;

 lemma_safe self::tll<a,b> <-> self::GG<a,b>;

/* 
# tll-lemma.ss -tp z3

Entailing lemma lem_16: Valid.

 tll<ll,lr> == self::node<_,null,lr> & self = ll
  or self::node<l,r,_> * l::tll<ll,z> * r::tll<z,lr> //& r!=null
	inv self!=null;

 GG<rr,t> == self::node<DP1,right,t> & right=null & rr=self
   or self::node<left,right,DP> * left::GG<rr,l> 
         * right::GG<l,t> & right!=null
   inv true;

It seems syntactic equivalence is used since we did not replace
G by tll.

# tll.ss --pred-en-equiv --pred-en-useless-para --pred-en-dangling


 tll<res,tt> == self::node<_,null,tt> & self = res
	or self::node<l,r,_> * l::tll<res,z> * r::tll<z,tt>
	inv self!=null;

[ H(x,t) ::=x::tree<>@M,
 G(x,res,t) ::= 
 x::node<DP1,right,t>@M&right=null & res=x
 or x::node<left,right,DP>@M * G(left,res,l) * G(right,l,t)&right!=null
 ]


*/
