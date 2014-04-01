data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred H1(node a, node@NI b).
HeapPred H2(node a, node@NI b).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

/*
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

lx8<g:node,s> == self!=s & self=null
  or self::node<_,nxt> * nxt::lx<self,s> & self!=s & self!=null ;

lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;
*/
lx1<s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx1<s> & self!=s 
inv true ;

HH<prev,sent> ==
  self::node<_,next> * next::lx1<sent> 
  * prev::HP0<sent>&self!=sent & self!=null
inv self!=null & self!=sent;

GG<cur':node,prev,sent> == (exists p: self::node<_,p>@M * p::HP0<cur'> & p=prev
     &cur'=sent)
inv self!=null;

/*
GG0<cur':node,sent> == self::node<_,p>@M * p::HP0<cur'> & cur'=sent
inv self!=null;

*/

HP0<sent> ==
  next::lx1<sent>@M * self::node<val,next>@M&self!=sent
  or emp&self!=sent & self=null
inv self!=sent;


//lemma_safe self::ll<s> & g=null -> self::lx<g,s>;

/*

[ H(cur,prev,sent) ::=cur::node<val,next>@M * next::lx1<sent>@M * 
  HP_1213(prev,sent)&cur!=sent & cur!=null,

 G(cur,cur',prev,prev',sent) ::= HP_1213(prev,cur') * prev'::node<val,prev>@M&cur'=sent,
 HP_1213(prev,sent) ::=
                       next::lx1<sent>@M * prev::node<val,next>@M&prev!=sent
                       or emp&prev!=sent & prev=null
                       ]
*/

void lscan( node@R cur, node@R prev, node sent)


  requires cur::HH<prev,sent>
  ensures prev'::GG<cur',prev,sent>;
//ensures prev'::GG0<cur',sent>;

/*
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
//EXPECTED 2 FAIL
  requires cur::node<_,n> * n::lx<_,sent> * prev::lx8<_,sent> & cur!=sent
  ensures prev'::node<_,p> * p::lx8<_,sent> & cur'=sent ;//'
*/

/*
//EXPECTED 3 (FAIL)
  requires cur::node<_,n> * n::lx1<_,sent> * prev::lx8<_,sent> & cur!=sent
  ensures prev'::node<_,p> * p::lx8<_,sent> & cur'=sent ;//'
*/

/*
  infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);
*/

//     infer [H1,H2,G]
//  requires cur::node<_,n> * H1(n,sent) * H2(prev,sent)

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
