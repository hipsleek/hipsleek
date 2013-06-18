data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> == p::ll<> & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwo<r>;

HeapPred HL(node a).

ltwoB<p:node> == HL(p) & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwoB<r>;

HeapPred H(node a, node b).
HeapPred G1(node a, node b, node c).
HeapPred G(node a, node b).

node zip (node l1, node l2)

 // infer [H,G]  requires H(l1,l2)  ensures  G(l1,l2);
  
// requires x::ltwo<y>  ensures res::ll<> * y::ll<> & res=x;
// requires x::ltwoA<y>  ensures res::ltwoA<y> & res=x;
requires l1::ltwoB<l2>  ensures res::ltwoB<l2> & res=l1;
{
   if (l1==null) return null;
   else {
	//assume false;
     int n1=l1.val;
     int n2=l2.val;
     l1.val = n1+n2;
     l1.next = zip(l1.next,l2.next);
     return l1;
   }
}

/*

===============================================================
# zip.ss

Problems, 
 (i) why ins't @NI printing?
 (ii) Why did we have:
            H1(x,y) x=null?


[ H1(x,y)&x!=null --> x::node<val_24_819,next_24_820>@M * 
  (HP_821(next_24_820,y)) * (HP_822(y,x))&true,
 (HP_821(next_24_820,y)) * (HP_822(y,x))&
  true --> y::node<val_25_826,next_25_827>@M * (HP_828(next_25_827,x))&true,
 HP_828(next_25_827,x)&true --> H1(next_24_820,next_25_827)&true,
 H1(x,y)&x=null & res=null --> G1(x,y,res)&true,
 y::node<val_25_826,next_25_827>@M * x::node<val_24_819,next_24_820>@M&
  res=x --> G1(x,y,res)&true]

======>

[ H1(x_1059,y_1060) ::= emp&x_1059=null,
 G1(x_1061,y_1062,res_1063) ::= 
 emp&res_1063=null & x_1061=null
 or y_1062::node<val_25_826,next_25_827>@M * 
    x_1061::node<val_24_819,next_24_820>@M&res_1063=x_1061
 ]


*/

