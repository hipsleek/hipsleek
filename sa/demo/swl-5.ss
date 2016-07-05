data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

lx<g,s> == self=g & s!=null
  //or self=null & self!=s // extra
  or self::node<_,nxt> * nxt::lx<g,s> & s!=null 
inv s!=null ;

void lscan(ref node cur, ref node prev, node sent)

requires cur::lx<null,sent> * prev::lx<sent,sent> & cur!=null 
ensures prev'::lx<null,sent>  & cur'=sent ;
requires cur::lx<sent,sent> * prev::lx<null,sent> & cur!=sent 
ensures prev'::lx<null,sent>  & cur'=sent ; 

/*
 requires cur::lx<a,sent> * prev::lx<b,sent> & cur!=a 
   //& (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent>  & cur'=sent ;

 requires cur::lx<a,sent> * prev::lx<b,sent> & cur!=a & cur!=null
   & (a=null & b=sent | a=sent & b=null)
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
      prev = null;
  }
  lscan(cur,prev,sent);

}

