data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

/*
ls<p> == self=p
    or self::node<_,nxt> * nxt::ls<p> & self!=p
inv true;
ll1<s> == self = null & self != s
	or self::node<_,p> * p::ll1<s> & self != s
inv self!= s;
*/


/*
lx<null,s> == self=null &  self!=s
  or self::node<_,nxt> * nxt::lx<null,s> & self!=s inv self!=s ;
lx<s,null> == self=s &  self!=null
  or self::node<_,nxt> * nxt::lx<s,null> & self!=null inv self!=null ;
*/

lx<g,s,M> == self=g & self!=s & M={} 
  or self::node<v,nxt> * nxt::lx<g,s,M1> & self!=g & self!=s & M=union(M1,{v})
  inv self!=s  ;

void lscan(ref node cur, ref node prev, node sent)
 requires cur::lx<a,b,M1> * prev::lx<b,a,M2> & cur!=a 
   & (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent,union(M1,M2)>  & cur'=sent ;

/*
requires cur::lx<null,sent> * prev::lx<sent,sent> & cur!=null 
ensures prev'::lx<null,sent>  & cur'=sent ;
requires cur::lx<sent,sent> * prev::lx<null,sent> & cur!=sent 
ensures prev'::lx<null,sent>  & cur'=sent ; 

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
      //dprint;
      prev = null;
      //dprint;
  }
  lscan(cur,prev,sent);

}

