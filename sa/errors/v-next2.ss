data node {
  node next;
}

node get_next(node x)
 requires x=null
 ensures  x!=null & flow __Error;
// requires x::node<q>@L ensures res=p;
{
  return x.next;
}
/*
# v-next2.ss --esl

Why sleek log is empty?

*/
