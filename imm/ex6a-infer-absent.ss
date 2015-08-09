data node {
 int val;
 node next;
}

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;


int join(node x, node y)
  infer [@imm_pre,@imm_post]
  requires x::node<a1,_>*y::node<a2,_>
  ensures x::node<_,_>*y::node<_,_> & res=a1+a2;
{ 
  return x.val+y.val;
} 

/*
# ex6a.ss

# need to fix this warning..

Checking procedure join$node~node... 
WARNING: _0:0_0:0:Z3 error message: (error "line 692 column 35: unknown function/constant P__1426")
!!! **infer.ml#1312:f: P__1426(ann_1425,ann_1424)

GOT
===
join$node~node
 EBase 
   exists (Expl)[](Impl)[ann_1424; ann_1425; a1; Anon_14; a2; 
   Anon_15](ex)[]x::node<a1,Anon_14>@ann_1424 * y::node<a2,Anon_15>@ann_1425&
   ann_1424=@L & ann_1425=@L & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     emp&{FLOW,(4,5)=__norm#E}[]

# What happen to res=a1+a2?


*/
