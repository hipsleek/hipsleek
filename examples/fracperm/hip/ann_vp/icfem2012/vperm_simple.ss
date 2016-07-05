/*
  Simple examples of variable permissions
  Variable permissions are automatically inferred.
 */

void foo(ref int x, ref int y)
  requires true //@full[x,y]
  ensures  x'=x+1 & y'=y+1; //& @full[x,y];
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
  requires true //@value[x] & @full[y]
  ensures y'=y+1; // & @full[y]; //'
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
  //can access i but j
  join(id);
  assert i'=0 & j'=1;
}
