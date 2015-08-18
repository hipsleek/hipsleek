data cell{
 int fst;
}

data pair{
  cell c1;
  cell c2;
}
/*
  relation P1(ann v1).*/
relation P2(ann v1, ann v2).
//relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

  int foo(cell c, pair d)
  infer [P2]
  requires c::cell<v>@a *d::pair<_,_>@a1 & P2(a,a1)
  ensures  c::cell<w>@b *d::pair<_,_>@a2 ;
{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   dprint;
   int tmp=2+foo(c,d);
   dprint;
   return tmp;
 } else return 0;
}


/*
(@A=imm_1321 & imm_1321<:a2_1318 & imm_1321!=a2_1318)


we could prune disjuncts like the following:
a=top & a<:b & a!=b 
a=bot & b<:a & a!=b
*/
