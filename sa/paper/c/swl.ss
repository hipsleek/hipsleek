data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred H1(node a, node@NI b).
HeapPred H2(node a, node@NI b).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).


  lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;

/*
lx7<g:node,s> ==
   self=null
  or self::node<_,nxt> * nxt::lx7<_,s> & g!=s & g!=null
inv true ;

*/
//lemma_unsafe self::lx7<_,next> & g=null -> self::lx<g,next>;

void lscan( node@R cur, node@R prev, node sent)

  requires cur::node<_,n> * n::lx<_,sent> * prev::lx<_,sent> //& cur!=sent
// ensures prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures prev'::node<_,p> * p::lx<_,sent> & cur'=sent ;//'
/*
requires cur::node<_,n> * n::lx<_,sent> * prev::lx7<_,sent>
// ensures prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures prev'::node<_,p> * p::lx7<_,sent> & cur'=sent ;//'
*/

/*
  infer [H,G]
  requires H(cur,prev,sent)
     infer [H1,H2,G]
  requires cur::node<_,n> * H1(n,sent) * H2(prev,sent)
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
