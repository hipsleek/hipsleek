
data cell{
 int fst;
}

relation P1(int v).
relation P2(int v,int r, int s).

int foo(cell x, cell y)
  infer [@imm_post]
  requires x::cell<v>@L * y::cell<_>
  ensures x::cell<v>@a * y::cell<_>@b & c = a & d = b & (3 = 3) & a = f;
{
 int z = x.fst;
 return z;
}

/*
Should get
Post Inference result:
foo$cell~cell
EBase 
exists (Expl)[](Impl)[v; Anon_11](ex)[]x::cell<v>@L * 
                      y::cell<Anon_11>@ann_1263&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                      EAssume 
                      (exists c_1242,d_1243,f_1246: emp&c_1242=@A & d_1243=@A & 3=3 & 
                              f_1246=@A & v=@A&{FLOW,(4,5)=__norm#E}[]
*/
