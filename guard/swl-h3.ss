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


lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=g & self!=s 
 inv self!=s ;

lx1<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::lx1<s> & self!=s 
 inv self!=s ;

lx2<g> == self=g & self!=null 
  or self::node<_,nxt> * nxt::lx2<g> & self!=g  
 inv self!=null ;

/*
lx<null,s>
lx1<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::lx1<s> & self!=s 
 inv self!=s ;

lx<s,null>

lx2<g> == self=g & self!=null 
  or self::node<_,nxt> * nxt::lx2<g> & self!=g  
 inv self!=null ;

 requires cur::lx<a,b> * prev::lx<b,a> & cur!=a 
  & (a=null & b=sent | a=sent & b=null)
*/

lxx<s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lxx<s> & self!=s
inv true ;

h1<s> == self::node<_,n>*n::lxx<s> 
 inv self!=null;

/*

*/

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

  infer [H1,H2,G1]
  requires H1(cur,sent) * H2(prev,sent)
  ensures G1(cur',prev',sent);

 requires cur::node<_,n>*n::lxx<sent> * prev::lxx<sent> 
 ensures prev'::node<_,p>*p::lxx<sent>  & cur'=sent ;

*/

 requires cur::lx1<sent>*prev::lx2<sent> & cur!=null
 ensures prev'::lx1<sent>  & cur'=sen & prev'!=nullt ;

 requires cur::lx2<sent>*prev::lx1<sent> & cur!=null
 ensures prev'::lx1<sent>  & cur'=sen & prev'!=nullt ;


/*

 requires cur::lx<a,b> * prev::lx<b,a> & cur!=a 
  & (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent>  & cur'=sent ;

 H1(cur,sent) ::= cur::node<val,next>@M * HP_952(next,sent),

 HP_952(cur,sent) ::= emp&cur=sent
    or cur::node<val,next>@M * HP_952(next,sent)&cur!=sent
    or emp&cur=null & cur!=sent

 H2(next,sent) ::= emp&next=null & next!=sent
      or next::node<val,prev>@M * H2(prev,sent)
      or DP_1059(next),

 G1(cur',prev',sent) ::= 
      prev'::node<val,prev1>@M * H2(prev1,cur') & cur'=sent,
  
 DP_1059(next) ::= NONE,


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
  dprint;
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  dprint;
  lscan(cur,prev,sent);

}
 

