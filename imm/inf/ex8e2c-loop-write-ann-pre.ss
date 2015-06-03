data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b ;
{
 int x = c.fst;
 if (x!=1) {
   c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e2c.ss

Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists b_1465,w_1466: c::cell<w_1466>@b_1465&
           

*/
