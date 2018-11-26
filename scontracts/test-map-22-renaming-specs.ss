data cell{
     int val;
}


void foo(ref cell yyy)
     requires yyy::cell<mmm> & mmm>0
     ensures  yyy'::cell<0>;
{
  yyy.val = 0;
}

void goo(ref cell xxx, ref cell zzz)
     requires xxx::cell<7> * zzz::cell<9>
     ensures  xxx'::cell<0> * zzz'::cell<0>;
{
  foo(xxx);
  foo(zzz);
}


/*
hip_include 'scontracts/mapprimitives.ss'

void foo8(ref mapping(int => int) mp)
   requires   [n] mp::Map<mp5> & mp5[0]=n & n>0
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=n+1);
{
  int x = select(mp,0)[int,int];// mp[0];
  // mp[0] = x + 1;
}

*/
