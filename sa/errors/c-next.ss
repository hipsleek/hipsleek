data node {
  node next;
}

node get_next(node x)

/*
case {
   x=null -> 
     ensures x=null & flow __Error;
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
  requires x::node<q>
  ensures x::node<q> & q=res;

{
  return x.next;
}

