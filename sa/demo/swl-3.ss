data node{
	int val;
	node next;
}

/*
ll<M> == self = null & M = {}
	or self::node<_,nxt> * nxt::ll<Mnxt> & M = union(Mnxt,{self})
inv true;

ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self=p & M=union(M2,{self})
inv true;
*/

HeapPred H(node a, node b, node@NI c).
PostPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).

HeapPred H1(node a, node@NI b).
HeapPred H2(node a, node@NI b).
PostPred G1(node a, node@NI b).
PostPred G2(node a, node@NI b).


void lscan(ref node cur, ref node prev, node sentinel)
/*
  requires cur::ls<M1,null> * prev::ls<M2,sentinel> * sentinel::node<_,_>@L & cur!=null
  ensures prev'::ls<M3,null> & cur'=sentinel & M3=union(M1,M2);
requires cur::ls<M1,sentinel> * prev::ls<M2,null> * sentinel::node<_,_>@L & cur!=sentinel
ensures prev'::ls<M3,null> & cur'=sentinel  & M3=union(M1,M2);
*/
/* cpy from swl-0b.slk
requires cur::ll<sent> * prev::lseg<sent> & cur!=null 
ensures prev'::ll<sent>  & cur'=sent ;
requires cur::lseg<sent> * prev::ll<sent> & cur!=sent 
ensures prev'::ll<sent>  & cur'=sent ; 
 */
  infer [H1,H2,G1,G2]
  requires H1(cur,sentinel) * H2(prev,sentinel)
  ensures G1(cur',sentinel) * G2(prev',sentinel);
{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel) return;
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sentinel);
}

/*
# swl-2.ss

hg !!!  synthesize: [G]
ExceptionFailure("iast.gather_type_info_heap :gather_type_info_heap: relation HP_885 cannot be found")Occurred!

Error(s) detected at main 
Stop Omega... 89 invocations caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("iast.gather_type_info_heap :gather_type_info_heap: relation HP_885 cannot be found")
Error(s) detected at main 


*/
