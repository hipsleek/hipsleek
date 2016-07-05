/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true;

HeapPred H1(node a).
HeapPred G2(node a, node b).

node insert(node x)

     infer [H1,G2]
     requires H1(x)
     ensures G2(res,x);

/*
  requires x::node<_,p>
 case { p= null -> ensures res::ll<> ;
  p!=null -> requires p::node<_,p1> * p1::ll<>
    ensures res::ll<>;
}
*/
{
    bool b = rand();
    node t = x.next;
    if (b) return t;
	else {
      if (t==null) return x;
      else {
         t = insert(t);
         return x;
      }
    }
}

bool rand() 
  requires true
  ensures res or !res; 

/*

[ G2(res_1009,x_1010) ::=(2;2;0) res_1009::node<val_32_974,next_32_975>@M * G2(t_993,next_32_975)&
next_32_975!=null & res_1009=x_1010
   \/ (1;2;0) res_1009::node<val_32_974,next_32_975>@M&res_1009=x_1010 & next_32_975=null
   \/ (1;0) HP_972(res_1009) * x_1010::node<val_32_970,res_1009>@M,
 H1(x_1008) ::= x_1028::node<val_32_970,next_32_971>@M * HP_976(next_32_971),
 HP_972(res) ::=(1;0) HP_976(res),
 HP_976(next_32_995) ::=(2;2;0) H1(next_32_995)&next_32_995!=null
   \/ (1;2;0) emp&next_32_995=null \/ (1;0) NONE]


*/
