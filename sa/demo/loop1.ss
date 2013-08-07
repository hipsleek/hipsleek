data cell{
	int val;
}


HeapPred P(cell a).
HeapPred G(cell a).

int loop (cell x)

    infer [P,G]  requires P(x)  ensures  G(x);

//  requires true ensures false;

{
   int r = loop(x);
   int n= x.val;
   return r+n;
}

/*
Obtained:

[ P(x)& XPURE(P(x)) --> P(x)&true,
 G(x')&true --> x'::cell<val_17_780>@M&true,
 x::cell<val_17_780>@M&true --> G(x)&true]

==========

 P(x) ::= emp& XPURE(P(x)),
 G(x_800) ::= x_800::cell<val_17_780>@M&true,
 G(x_801) ::= x_801::cell<val_17_780>@M&true]

===========
PROBLEM : why G(..) twice, and why XPURE(P(x))?

Should it be:

 P(x) <--> P(x)
 G(x) <--> x::cell<_>

 requires false
 ensure x::cell<_>;

 converted to:
 
 requires true
 ensures  false;


*/

