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

/* below fails - OK*/
void foo2(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=7);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}


/* below succeeds - NOT OK!!! */
void foo3(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=2);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}
