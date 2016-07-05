data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).


ll<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::ll<s> & self!=s 
inv self!=s ;

lseg<p> == self=p 
  or self::node<_,nxt> * nxt::lseg<p> & self!=p 
inv true;

lx7<g:node,s> ==
    self=null
  or self::node<_,nxt7> * nxt7::lx7<_,s> & g!=s & g!=null
inv true ;

lx8<s> == self!=s & self=null
  or self::node<_,nxt> * nxt::lx1<s> & self!=s & self!=null ;

lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;

lx1<s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx1<s> & self!=s 
inv true ;

//lemma_safe self::ll<s> & g=null -> self::lx<g,s>;

void lscan( node@R cur, node@R prev, node sent)

/* OK
requires cur::ll<sent> * prev::lseg<sent> & cur!=null 
ensures prev'::ll<sent>  & cur'=sent ;
requires cur::lseg<sent> * prev::ll<sent> & cur!=sent 
ensures prev'::ll<sent>  & cur'=sent ;
*/

/* FAIL
  requires cur::node<_,n> * n::lx<_,sent> * prev::lx<_,sent> & cur!=sent
  ensures prev'::node<_,p> * p::lx<_,sent> & cur'=sent &prev'!=sent;//'
*/

/*
//EXPECTED 1 (FAIL)
  requires cur::node<_,n> * n::lx<_,sent> * prev::ll<sent> & cur!=sent
  ensures prev'::node<_,p> * p::ll<sent> & cur'=sent ;//'
*/
/*
//EXPECTED 2
  requires cur::node<_,n> * n::lx<_,sent> * prev::lx8<_,sent> & cur!=sent
  ensures prev'::node<_,p> * p::lx8<_,sent> & cur'=sent ;//'
*/

/*
//EXPECTED 3
  requires cur::node<_,n> * n::lx1<sent> * prev::lx8<sent> & cur!=sent
  ensures prev'::node<_,p> * p::lx8<sent> & cur'=sent ;//'
*/

  infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);


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
      dprint;
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
