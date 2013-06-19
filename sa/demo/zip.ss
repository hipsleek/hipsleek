data node{
	int val;
	node next;
}

//ll<> == self = null  or self::node<_, q> * q::ll<>;

/*
ltwo<p:node> == p::ll<> & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwo<r>;
*/

HeapPred HL(node a).
HeapPred H(node a, node b).
HeapPred G1(node a, node b, node c).

ltwoB<p:node> == HL(p) & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwoB<r>;

node zip (node x, node y)
//  infer [H,G1]  requires H(x,y)  ensures  G1(x,y,res);
// requires x::ltwo<y>  ensures res::ll<> * y::ll<> & res=x;
// requires x::ltwoA<y>  ensures res::ltwoA<y> & res=x;
//requires x::ltwoB<y>  ensures res::ltwoB<y> & res=x;
//requires l1::ltwoB<l2>  ensures res::ltwoB<l2> & res=l1;
infer [HL] requires x::ltwoB<y>  ensures res::ltwoB<y> & res=x;
{
   if (x==null) return x;
   else {
	//assume false;
     int n1=x.val;
     int n2=y.val;
     x.val = n1+n2;
     x.next = zip(x.next,y.next);
     return x;
   }
}

/*

verification fails.

!! after remove redundant:[]
Procedure zip$node~node result FAIL-1


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

