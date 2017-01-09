
data cell {
 int fst;
 int snd;
}

cell trick(cell y)
infer [@imm_post]
requires y::cell<_,_>@A
ensures res::cell<_,_>;
{
   y = new cell(3, 4);
   y.fst = 4;
   return y;
}
