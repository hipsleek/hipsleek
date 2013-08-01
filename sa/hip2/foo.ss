/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

HeapPred H(node a).
HeapPred G(node a,node a).

bool rand()
  requires true
  ensures !res or res;

/* function to delete the node after the head in a circular list */
node foo(node x)
/*
   requires x::node<_,q>
   ensures x::node<_,q> & res=q;
*/
infer [H,x,G] 
requires H(x)
ensures G(x,res);
/*

*/
{
	node tmp;
        if (rand()) {
         tmp=x.next;
        } else {
         tmp=x;
        };
        return tmp;
}

/*
[ H(x)&true --> x::node<val_31_786,next_31_787>@M * (HP_788(next_31_787))&true,
 (HP_788(res)) * x::node<val_31_786,res>@M&true --> G(x,res)&true,
 H(x)&res=x --> G(x,res)&true]


[ H(x_809) ::= 
     x_809::node<val_31_786,next_31_787>@M& XPURE(HP_788(next_31_787)),
  G(x_810,res_811) ::= 
  emp&res_811=x_810 &  XPURE(H(x_810))
  or x_810::node<val_31_786,res_811>@M& XPURE(HP_788(res_811))
]

*/