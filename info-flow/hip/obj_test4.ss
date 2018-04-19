/* bool_sec eq(int_sec a, int_sec b) */
/*   requires a::int_sec<va,sa> * b::int_sec<vb,sb> */
/*   ensures  res::bool_sec<vres,sres> & vres=(va=vb) & sres<=sr & sr=max(sa,sb); */
/* { */
/*   return a==b; */
/* } */

data node {
  int v;
  node n;
}

int_sec add(int_sec x, int_sec y)
  requires x::int_sec<vx,sx> * y::int_sec<vy,sy>
  ensures  res::int_sec<vr,sr> & vr=vx+vy & sr<=_sr & _sr=max(sx,sy);
{
  return x+y;
}
