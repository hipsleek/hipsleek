    
data node {
    node prev; 
    node next; 
    }

HeapPred H1(node a,node@NI b).
PostPred G1(node a,node@NI b).

dll<prev> == 
  self=null or 
  self::node<prev,n>* n::dll<self>;

bool check_dll (node l, node prv)
  //requires l::dll<prv>@L ensures  res;
  infer [H1,G1] requires H1(l,prv) ensures G1(l,prv) & res;
{
	if (l==null) return true;
	else return (l.prev==prv) && check_dll(l.next,l);
}

/*
# check-dll.ss

dll is not working for the following reasons
  (i) there are some spurious relational assumption
       perhaps from early contra (which may be correct
       but make result looks complex)
 (ii) it seems cannot handle back-pointers for
     pre-predicate properly; as that seem to require 
     magic wand to capture the context of some pointers.

For both these rules, the value of l on the RHS
need to be located to support unfolds that find
the correct back-pointers.
 H_1(next_9,prv@NI)&prev_8=prv --> H1(next_9,l@NI),
 H_1(next_9,prv@NI) --> H1(next_9,l@NI),

Just as an example, for the first case, it seems that
we would need the following rule instead:

It seems that we need to capture instead:
 H_1(next_9,prv@NI)&prev_8=prv -->
     l::node<prev_8,next_9> --*  H1(next_9,l@NI),
which simplifies to:
 H_1(next_9,prv@NI) -->
     l::node<prv,next_9> --*  H1(next_9,l@NI),



GOT
===
 [ H1(l_1,prv_2) ::= 
 H1(next_4,l_983) * l_1::node<prev_5,next_4>@M
           ^^^^^^ this should be equal to l_1
  & forall(l:((prv_2>=prev_5 | l=null)) & ((prev_5>=prv_2 | 
    l=null))) 
 or emp&l_1=null
 ,
 G1(l_4,prv_5) ::= 
 H_0(prev_8,prv_5) * l_4::node<prev_8,next_9>@M 
   * G1(next_9,l_4)&prev_8=prv_5
 or emp&l_4=null
 ,
 H_0(prev_8,prv) ::= NONE]

which came from
===============
 H1(l,prv@NI)&l!=null --> l::node<prev_8,next_9>@M * 
   H_0(prev_8,prv@NI) * H_1(next_9,prv@NI),
 H_1(next_9,prv@NI)&prev_8=prv --> H1(next_9,l@NI),
 H_1(next_9,prv@NI) --> H1(next_9,l@NI),

 H1(l,prv@NI)&l=null --> G1(l,prv@NI),
 H_0(prev_8,prv@NI) * l::node<prev_8,next_9>@M * 
  G1(next_9,l@NI)&prev_8=prv --> G1(l,prv@NI),
 H_0(prev_8,prv@NI) --> emp&forall(l:((prv>=prev_8 | l=null)) & 
  ((prev_8>=prv | l=null)))]




*/
