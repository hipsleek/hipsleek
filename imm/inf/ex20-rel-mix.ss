
data cell{
 int fst;
}

relation P1(int v).
relation P2(int v,int r, int s).

int foo(cell x, cell y)
  infer [@imm_post]
  requires x::cell<v>@L * y::cell<_>
  ensures x::cell<v>@a * y::cell<_>@b & c = a & d = b & (3 = 3);
{
 int z = x.fst;
 return z;
}
