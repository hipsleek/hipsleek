data node{
	int val;
	node next;
}

HeapPred H1(node a).
HeapPred G1(node a, node b).

node foo (node c)
  infer[H1,G1] 
  requires H1(c) 
  ensures G1(res,c);
{
    return c.next;
}

/*
[ H1(c_787) ::= c_787::node<val_14_777,next_14_778>@M& XPURE(HP_779(next_14_778)),
 G1(next_14_788,c_789) ::= c_789::node<val_14_777,next_14_788>@M& XPURE(HP_779(next_14_788))]

Instead of:

[ H1(c)&true --> c::node<val_14_743',prev_14_744',next_14_745'>@M * 
  (HP_765(prev_14_744')) * (HP_766(next_14_745'))&true,
 c::node<val_14_770,prev_14_771,res>@L * (HP_765(prev_14_771)) * 
  (HP_766(res))&true --> G1(res,c)&true]

Is more readable version below achievable?
  - replace unaccessed predicate HP_765,HP_766 by variable
  - shorten name for readability

    H1(c)    ::= c::node<val,p,n>@M
  G1(res,c)  ::= c::node<val,p,n>@M & res=n,

*/

