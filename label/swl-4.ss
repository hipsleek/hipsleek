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

lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=g & self!=s 
//  inv self!=s & (g!=self & s!=self | g=self);
  inv self!=s;

/*
lx<null,s> == self=null &  self!=s
  or self::node<_,nxt> * nxt::lx<null,s> & self!=s inv self!=s ;
lx<s,null> == self=s &  self!=null
  or self::node<_,nxt> * nxt::lx<s,null> & self!=null inv self!=null ;
*/

void lscan(ref node cur, ref node prev, node sent)
 requires cur::lx<a,b> * prev::lx<b,a> & cur!=a 
   & (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent>  & cur'=sent ;

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
      dprint;
      prev = null;
      //dprint;
  }
  lscan(cur,prev,sent);

}

