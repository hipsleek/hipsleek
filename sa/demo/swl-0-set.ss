data node{
	int val;
	node next;
}

/*
ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self!=p & M=union(M2,{self})
inv true;
*/

ll<s,B> == self=null & self!=s & B={}
  or self::node<v,nxt> * nxt::ll<s,B1> & self!=s & B=union({v},B1)
inv self!=s ;

lseg<p,B> == self=p & B={}
  or self::node<v,nxt> * nxt::lseg<p,B1> & self!=p & B=union({v},B1)
inv true;

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

void lscan(ref node cur, ref node prev, node sent)
  requires cur::ll<sent,B1> * prev::lseg<sent,B2> & cur!=null 
ensures prev'::ll<sent,union(B1,B2)>  & cur'=sent ;
requires cur::lseg<sent,B1> * prev::ll<sent,B2> & cur!=sent 
ensures prev'::ll<sent,union(B1,B2)>  & cur'=sent ;

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
      prev = null;
      lscan(cur,prev,sent);
  }
  else {
    //assume false;
      lscan(cur,prev,sent);
  }
}

