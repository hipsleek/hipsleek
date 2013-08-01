data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

  lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;

//lemma self::node<_,p> * p::lx<_,s> -> self::node<_,p> * p::lx<_,s> & self!=s;

void lscan(ref node cur, ref node prev, node sent)
  requires cur::node<_,n> * n::lx<_,sent> * prev::lx<_,sent> & cur!=sent
// ensures prev'::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
// ensures cur::node<_,prev> * prev::lx<_,sent>  &cur=prev' & cur'=sent;// &prev'!=sent ;//'

/*
lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=s 
inv self!=s ;
requires cur::lx<a,sent> * prev::lx<b,sent> & cur!=a 
   & (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent>  & cur'=sent ;

 */
/*
  infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);
*/
{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
      //assume false;
      return;
  }
  if (cur == null) {
      // change direction;
      cur = prev;
      // dprint;
      prev = null;
      // dprint;
  }
  lscan(cur,prev,sent);

}
/*
void main(node x, node pre, node sent)
  requires x::lx<null,sent> & x!=sent & x!=null & pre=sent
 ensures true ;
{
  lscan(x, pre, sent);
}
*/
