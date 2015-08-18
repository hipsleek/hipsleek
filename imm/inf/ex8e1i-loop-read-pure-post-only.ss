data cell{
 int fst;
}


relation P(int v1, int v2, int v3).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P]
  requires c::cell<v>
//  ensures c::cell<v> & P(v,res); //c::cell<w>@b & b=@L  ;
  ensures c::cell<w> & (res = 0 & v<=3 & w=v) | (res=v-3 & v>3);// & w+1=v);

{
 int x = c.fst;
 if (x>3) {
   c.fst =c.fst-1;
   int tmp=1+foo(c);
   dprint;
   return tmp;
 } else return 0;
}



int foo1(cell c)
  infer [P]
  requires c::cell<v> & v>=3
//  ensures c::cell<v> & P(v,res); //c::cell<w>@b & b=@L  ;
  ensures c::cell<w> & P(v,w,res);

{
 int x = c.fst;
 if (x>3) {
   c.fst =c.fst-1;
   int tmp=1+foo1(c);
   dprint;
   return tmp;
 } else return 0;
}
