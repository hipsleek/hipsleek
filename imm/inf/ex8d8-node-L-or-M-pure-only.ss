data cell{
 int fst;
}

relation P1(int v).
relation P2(int v,int r, int s).
relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@M & P1(v)
     //ensures c::cell<w>@b & P3(b,v,res,w);
     ensures c::cell<w>@M & P2(v,res,w)  ;
{
 int x = c.fst;
 if (x>0) c.fst = 5;
 return x;
}

/*

where do the two imm rel assumption come from?

*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [P2]: ( P2(v,res,w_1202)) -->  v<:@A & res<:@A & w_1202<:@A,
RELASS [P1]: ( P1(v)) -->  v<:@A,
RELDEFN P2: ( w_1202=5 & v=res & 1<=res & P1(v)) -->  P2(v,res,w_1202),
RELDEFN P2: ( w_1202=res & v=res & res<=0 & P1(v)) -->  P2(v,res,w_1202)]
*************************************

*/
