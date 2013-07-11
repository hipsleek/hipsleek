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

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

void lscan(ref node cur, ref node prev, node sent)
requires cur::ll<sent> * prev::lseg<sent>
//*sent::node<_,_>@L 
   & cur!=null 
ensures prev'::ll<sent>  & cur'=sent ;
requires cur::lseg<sent> * prev::ll<sent> 
//* sent::node<_,_>@L 
    & cur!=sent 
ensures prev'::ll<sent>  & cur'=sent ;
//ensures prev'::ll<> * sent::node<_,_> & cur'=sent ;

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

