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
# id.ss

GOT:
[ P(x)&res=x --> G(x,res)&true]

WHY are both treated as UNKNOWN!

[ P(a) ::=NONE,
 G(a,r) ::=NONE]

P/Q should be normal pre/post; and have
defns:

  P(a) ::= emp.
 G(a,r) ::= a=res




P(x) - pre-condition cannot be dangling
  'cos x is from input

P(x,y) --> x::node<_,q>*HP1(q,y@NI)*HP2(y,x@NI)
  HP1(..) could be dangling pred
  HP2(..) is non-dangling 'cos y is from input


 requires P(x,y)
 ensures  G(x,y,res)
 

 P(x)&res=x --> G(x,res)&true]

 P(x) --> emp
 res=x --> G(x,res)

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

