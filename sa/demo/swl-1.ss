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
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).


void lscan(ref node cur, ref node prev, node sentinel)
/*
  requires cur::ls<M1,null> * prev::ls<M2,sentinel> * sentinel::node<_,_>@L & cur!=null
  ensures prev'::ls<M3,null> & cur'=sentinel & M3=union(M1,M2);
requires cur::ls<M1,sentinel> * prev::ls<M2,null> * sentinel::node<_,_>@L & cur!=sentinel
ensures prev'::ls<M3,null> & cur'=sentinel  & M3=union(M1,M2);
*/
  infer [H,G]
  requires H(cur,prev,sentinel)
  ensures G(cur,cur',prev,prev',sentinel);
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
# swl-i.ss

was there a pre-proof obligation that failed?

Context of Verification Failure: 1 File "swl-i.ss",Line:29,Col:10
Last Proving Location: 1 File "swl-i.ss",Line:45,Col:2

ERROR: at _0:0_0:0 
Message: self of HP_880 cannot have its type determined
 
ExceptionFailure("self of HP_880 cannot have its type determined")Occurred!

Error(s) detected at main 
Stop Omega... 70 invocations caught
(Program not linked with -g, cannot print stack backtrace)

[ H(cur,prev,sentinel@NI) --> cur::node<val_33_878,next_33_879>@M * 
  HP_880(next_33_879,prev@NI,sentinel@NI) * HP_881(prev,cur@NI),
                                                     ^^^ sentinel?

 HP_881(prev,cur@NI) * cur::node<val_33_878,prev>@M&cur=cur_887 & 
  cur'=cur_887 & prev'=null --> H(cur',prev',sentinel@NI),

 HP_880(next_33_879,prev@NI,sentinel@NI) * HP_881(prev,cur@NI) * 
  cur::node<val_33_878,prev>@M&cur=cur_887 & cur'=next_33_879 & 
  cur'!=sentinel & cur'!=null --> H(cur',cur_887,sentinel@NI),

 HP_880(next_33_879,prev@NI,sentinel@NI) * HP_881(prev,cur@NI) * 
  cur::node<val_33_878,prev>@M&cur=prev' & cur'=next_33_879 & 
  cur'=sentinel --> G(cur,cur'@NI,prev,prev'@NI,sentinel@NI),

 HP_880(next_33_879,prev@NI,sentinel@NI) * HP_881(prev,cur@NI) * 
  cur::node<val_33_878,prev>@M&cur=prev' & cur'=next_33_879 & 
  cur'=sentinel --> G(cur,cur'@NI,prev,prev'@NI,sentinel@NI),

 HP_880(next_33_879,prev@NI,sentinel@NI) * 
  G(prev_899,cur'@NI,prev_911,prev'@NI,sentinel@NI)&cur=prev_899 & 
  next_33_879!=sentinel & prev_911=null & 
  next_33_879=null --> G(cur,cur'@NI,prev,prev'@NI,sentinel@NI),

 G(next_33_879,cur'@NI,cur,prev'@NI,sentinel@NI)&next_33_879!=sentinel & 
  next_33_879!=null --> G(cur,cur'@NI,prev,prev'@NI,sentinel@NI)
 ]

*/
