data node{
	int val;
	node next;
}

/*
ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self!=p & M=union(M2,{self})
inv true;
*/

lseg<p> == self=p 
  or self::node<_,nxt> * nxt::lseg<p> & self!=p 
inv true;

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).


void lscan(ref node cur, ref node prev, node sent)
/*
  requires cur::ls<M1,null> * prev::ls<M2,sent> & cur!=null
  ensures prev'::ls<M3,null> & cur'=sent & M3=union(M2,M2);
requires cur::ls<M1,sent> * prev::ls<M2,null> & cur!=sent
ensures prev'::ls<M3,null> & cur'=sent  & M3=union(M2,M2);
*/

 requires cur::lseg<n> * sent::node<_,_>@L & cur!=null
 case {
  n=null ->  
       requires prev::lseg<sent> 
       ensures  prev'::lseg<null> & cur'=sent;
  n!=null ->  case {
         n=sent -> requires prev::lseg<null> & cur!=sent
              ensures prev'::lseg<null> & cur'=sent;
         n!=sent -> requires false ensures false;
  }
 }
/*
requires cur::lseg<null> * prev::lseg<sent> * sent::node<_,_,_>@L & cur!=null
ensures prev'::lseg<null> & cur'=sent ;
requires cur::lseg<sent> * prev::lseg<null> * sent::node<_,_,_>@L & cur!=sent 
ensures prev'::lseg<null> & cur'=sent ;
*/

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
  if (cur == sent) return;
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);
}

/*
# swl-i.ss



*/
