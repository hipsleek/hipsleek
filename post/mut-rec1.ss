relation Uf1(int n, int r).
  relation Uf2(int n, int r).

/*
  int foo1(int n)
infer[Uf1]
requires true
  ensures Uf1(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo1(n-1);
}

  int foo2(int n)
infer[Uf2]
requires true
  ensures Uf2(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo2(n-1);
}
*/

  int foo1(int n)
infer[Uf1]
requires true
  ensures Uf1(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo2(n-1);
}

  int foo2(int n)
infer[Uf2]
requires true
  ensures Uf2(n,res);
{
  if (n <= 0) return 0;
  else return 1+foo1(n-1);
}
