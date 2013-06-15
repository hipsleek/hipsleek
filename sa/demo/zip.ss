data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> == p::ll<> & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwo<r>;

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node zip (node x, node y)
/*
  infer [H1,G1]
  requires H1(c,y)
  ensures  G1(c,y);
*/
  requires x::ltwo<y>
  ensures res::ll<> * y::ll<> & res=x;
{
   if (x==null) return null;
   else {
     int n1=x.val;
     int n2=y.val;
     x.val = n1+n2;
     x.next = zip(x.next,y.next);
     return x;
   }
}

/*

Why did we have this error in hip but when transferred to
SLEEK, it went through?

checkentail x::ltwo<y_818>@M[0][Orig][LHSCase]&y=y_818 & x=null & v_bool_23_798' & 
x=null & v_bool_23_798' & v_null_23_781'=null & res=v_null_23_781'&
{FLOW,(22,23)=__norm}[]
 |-  res::ll@M[0][Orig][LHSCase] * y::ll@M[0][Orig][LHSCase]&true&
{FLOW,(22,23)=__norm}[]. 
res:  failctx
         fe_kind: MAY
         fe_name: separation entailment
         fe_locs: {
                   fc_message: mis-matched LHS:ltwo and RHS: ll
                   fc_current_lhs_flow: {FLOW,(22,23)=__norm}}


*/

