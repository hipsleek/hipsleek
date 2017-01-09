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
  ensures x=null & flow __Error;

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
# v-next.ss --efa

Why is about complete spec not working??

Checking procedure get_next$node... Proving binding in method get_next$node for spec  EAssume 2
   emp&{FLOW,(26,27)=__norm}[]
   , Line 11

( []) bind: node  x'::node<next_15_1183'> cannot be derived from context
v-next.ss_15:9_15:15

*/
