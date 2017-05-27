pred_prim security<i : int>;

data X {
  int f1;
  int f2;
}

data Y {
  int s1;
  int s2;
}

int f(int h, int l)
  requires h::security<H> * l::security<L> & H <= 1 & L <= 0
  ensures res::security<R> & R <= 0;
{
  if (h == 1) {
    l = 2;
  }
  else {
    l = 1;
  }

  return l;
}

int afun1()
  requires true
  ensures res::security<R> & R <= 0;
{
  return 1;
}

int afun2()
  requires true
  ensures res::security<R> & R <= 1;
{
  return 1;
}

int afun3(int p)
  requires true
  ensures res::security<R> & R <= 0;
{
  return p;
}

int afun4(int p)
  requires p::security<P> & P <= 0
  ensures res::security<R> & R <=0;
{
  return p;
}

int afun5(int p)
  requires p::security<P> & P <= 0
  requires res::security<R> & R <= 1;
{
  return p;
}