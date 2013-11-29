data node{
	int val;
	node next;
}

/*
ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self!=p & M=union(M2,{self})
inv true;
*/

ll<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::ll<s> & self!=s 
inv self!=s ;

lseg<p> == self=p 
  or self::node<_,nxt> * nxt::lseg<p> & self!=p 
inv true;

lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;

HeapPred H(node a, node b, node@NI c).
HeapPred H1(node a,  node@NI c).
HeapPred H2(node a,  node@NI c).
PostPred G(node a, node ra, node b, node rb, node@NI c).

PostPred G1(node ra,  node rb, node@NI c).

void lscan( node@R cur, node@R prev, node sent)
/*
 requires cur::node<_,n> * n::lx<_,sent> * prev::lx<_,sent> & cur!=sent
// ensures prev'::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures  prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
*/

  infer [H1,H2,G1]
  requires H1(cur,sent) * H2(prev,sent)
  ensures G1(cur',prev',sent);

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
  //dprint;
  if (cur == null) {
      // change direction;
    node tmp = cur;
      cur = prev;
      //prev = null;
      prev = tmp;
  }
  //dprint;
  lscan(cur,prev,sent);

}

