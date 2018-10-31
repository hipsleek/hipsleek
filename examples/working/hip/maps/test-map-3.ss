hip_include 'scontracts/mapprimitives.ss'


/* below succeeds - OK */
void foo1(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=5);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}

/* below fails - OK */
void foo2(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=7);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}


/* below fails - OK */
void foo3(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=2);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}


/* below fails - OK*/
void foo4(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=12345678900);
{
  mp[0] = 2;
  mp[0] = 123456789000;
  dprint;
}


/* below succeeds - OK*/
void foo5(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=55555);
{
  mp[0] = 55555;
  dprint;
}


/* below fails - OK*/
void foo6(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=7);
{
  dprint;
}


/* below fails - OK*/
void foo7(ref mapping(int => int) mp)
   requires   mp::Map<mp9>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=5);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}


/* below fails - OK*/
void foo8(ref mapping(int => int) mp)
   requires   [n] mp::Map<mp5> & mp5[0]=n & n>0
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=n+1);
{
  mp[0] = mp[0] + 1;
}
