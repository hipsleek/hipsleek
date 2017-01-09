data node {
  node next;
}

node get_next(node x)
/*
 case {
   x=null -> 
     ensures x!=null & flow __Error;
   x!=null -> 
     requires x::node<q> 
     ensures x::node<q> & res=q;
}
*/
/*
requires x=null or x::node<q>
ensures x=null & flow __Error or x::node<q> & q=res;
*/
  requires x=null
  ensures x!=null & flow __Error;
/*
  requires x::node<q>
  ensures x::node<q> & q=res;
*/
//  requires x=null ensures true  & flow __Error;
// requires x::node<q>@L ensures res=p;
{
  return x.next;
}
/*
# v-next5b1.ss --esl

This is wrong. How can x=null |- x!=null
in the post-condition?

--esl only contain a BIND and no post-condition proving!
What is happening here?

id: 0; caller: []; line: 28; classic: false; kind: BIND; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail emp&x=null & x'=x&{FLOW,(3,4)=__norm}[]
 |-  x'::node<next_28_1203'>&{FLOW,(1,28)=__flow}[]. 
res:  failctx
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: do_unmatched_rhs : x'::node<next_28_1203'>
                   fc_current_lhs_flow: {FLOW,(5,9)=__Error}}
[[ COND ==>  UnmatchedRHSData ==> ]]true
*/
