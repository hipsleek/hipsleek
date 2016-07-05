data cell{
	int val;
}


HeapPred P(cell a).
HeapPred G(cell a).

int loop (cell x)
  infer [P,G]  requires P(x)  ensures  G(x);
/*
  requires x::cell<a>
  ensures false;
*/
{
   int n1 = x.val;
   int r = loop(x);
   return r+n1;
}

/*
Obtained:

[ P(x)&true --> x::cell<val_16_777>@M&true,
 x::cell<val_16_777>@M&true --> P(x)&true,
 G(x)&true --> G(x)&true]

==========

P(x_800) ::= x_800::cell<val_16_777>@M&true
G(x) ::= G(x)
     ::= false
*/

