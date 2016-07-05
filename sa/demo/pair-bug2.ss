data cell{
	int val;
}

//ll<> == self = null  or self::node<_, q> * q::ll<>;

HeapPred H1(cell a, cell b).
HeapPred G1(cell a, cell b).
HeapPred P1(cell a).
HeapPred P2(cell a).

int sum (cell x, cell y)
  infer [P1,P2,G1]  requires P1(x) * P2(y)  ensures  G1(x,y);
//  infer [H1,G1]  requires H1(x,y)  ensures  G1(x,y);
/*
  requires x::cell<a>*y::cell<b>
  ensures x::cell<a>*y::cell<b> & res=a+b;
*/
{
   int n1 = x.val;
   int n2 = y.val;
   return n1+n2;
}

/*
Obtained:

 checkentail x::cell<val_20_784>@M[Orig] * y::cell<val_21_788>@M[Orig]&
v_int_22_765'=val_21_788+val_20_784 & res=v_int_22_765'&
{FLOW,(22,23)=__norm}[]
 |-  G1(x,y)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ x::cell<val_20_784>@M&true --> G1(x,y)&true]

which seems to have lost y::cell<..>. I suppose, we may need to
try capture both sets of links from x,y for folding; so that we
will have:

 x::cell<val_20_784>@M * y::cell<_> --> G1(x,y)&true]

We probably can try to traverse separately.


*/

