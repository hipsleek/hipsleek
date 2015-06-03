data cell{
 int fst;
}

relation P1(ann v1).
  relation P2(ann v1, ann v2,int v,int r).

int foo(cell c)
/*
  requires c::cell<v>@L
  ensures res=v;
*/
  infer [P1]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & res=v;
{
 int x = c.fst;
 return x;
}
/*
# ex3d5.ss

  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & P2(a,b,res)  ;

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( res=v & b_1458=a & a<:@L & P1(a)) -->  P2(a,b_1458,v,res)]

# I guess weakest pre means a=@L, giving:
   P1(a) ::= a=@L
# Substituting this into P2 gives:
    ( res=v & b_1458=a & a<:@L & a=@L) -->  P2(a,b_1458,v,res)]
    ( res=v & b_1458@L & a=@L) -->  P2(a,b_1458,v,res)]
 Looking for strongest post gives us:
   P2(a,b_1458,v,res) <-- res=v & b_1458@L & a=@L  
# After that, we can remove @L nodes from post-condition.

foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a<:@L & a<:@L & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1457,b_1458: c::cell<v_1457>@b_1458&v_1457=v & res=v & 
           b_1458=a & a<:@L&{FLOW,(4,5)=__norm#E}[]

Expects:
  requires c::cell<v>@L
  ensures res=v;

*/
