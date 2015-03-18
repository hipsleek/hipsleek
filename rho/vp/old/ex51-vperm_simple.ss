/*
  Simple examples of variable permissions
 */

void foo(ref int x, ref int y)
  requires @full[x,y]
  ensures  @full[x,y] & x'=x+1 & y'=y+1; //& ;
{
  x++;
  y++;
}

void f()
requires true
  ensures true;
{
  int id;
  int i,j,k;
  i=0;j=0;k=0;
  id = fork(foo,i,j);
  //can not access i and j here
  join(id);
  assert i'=1 & j'=1;
}

void foo2(int x, ref int y)
  requires @value[x] * @full[y] //
  ensures @full[y] & y'=y+1; // & ; //'
{
  x++;
  y++;
}

void f2()
requires true
  ensures true;
{
  int id;
  int i,j,k;
  i=0;j=0;k=0;
  id = fork(foo2,i,j);
  //can acces i but j
  join(id);
  assert i'=0 & j'=1;
}
