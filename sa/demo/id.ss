data cell{
	cell val;
}


HeapPred P(cell a).
  HeapPred G(cell a, cell r).

cell id (cell x)
 infer [P,G]  requires P(x)  ensures  G(x,res);
//requires emp  ensures  emp & x=res;
{
  return x;
}

/*

A predicate is non-dangling if it is being used
for a pre-pred definition.
I suppose dangling classification may have to be
done after base-case splitting.


 P(..) & p --> RHS



[ P(x)&res=x --> G(x,res)&true]

====

[ P(x) ::= emp& XPURE(P(x)),
 G(x_773,res_774) ::= emp&res_774=x_773 &  XPURE(P(x_773))]

====

Sufficient to use:

  P(x) --> emp
  res=x --> G(x,res)

====>
  P(x)     <--> emp
  G(x,res) <--> res=x

*/

