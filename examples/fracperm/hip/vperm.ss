void foo(ref int x, ref int y)
   requires @p_ref[x] & @p_ref[y]
ensures  @full[x] & @full[y] & x'=x+1 & y'=y+1;
{
  x++;
  y++;
}

void foo2(int x, ref int y)
   requires @p_ref[y]
ensures @full[y] & y'=y+1; //'
{
  x++;
  y++;
}

void main()
requires true
  ensures true;
{
  int i,j,k;
  i=0;j=0;k=0;
  /* foo(i,j); */
  /* assert i'=1 & j'=1; */
  foo2(i,j);
  assert i'=0 & j'=1;
}
