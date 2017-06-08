pred_prim security<i : int>
  inv 0 <= i & i <= 1;

int const_int(int i)
  requires true
  ensures res::security<R> & res=i & R<=0;

bool const_bool(bool b)
  requires true
  ensures res::security<R> & res=b & R<=0;

bool eqv(int a, int b)
  requires a::security<A>@L * b::security<B>@L
  case {
    a = b -> ensures res::security<R> & res & R = max(A, B);
    a != b -> ensures res::security<R> & !res & R = max(A, B);
  }

bool lt(int a, int b)
  requires a::security<A>@L * b::security<B>@L
  case {
    a < b -> ensures res::security<R> & res & R = max(A, B);
    a >= b -> ensures res::security<R> & !res & R = max(A, B);
  }

int plus(int a, int b)
  requires a::security<A>@L * b::security<B>@L
  ensures res::security<R> & res = a + b & R = max(A, B);

int minus(int a, int b)
  requires a::security<A>@L * b::security<B>@L
  ensures res::security<R> & res = a - b & R = max(A, B);

int if_then_else(bool b, int i, int j)
  requires b::security<B>@L * i::security<I>@L * j::security<J>@L
  case {
    b -> ensures res::security<R> & res = i & R = max(max(B, I), J);
    !b -> ensures res::security<R> & res = j & R = max(max(B, I), J);
  }


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
  l = if_then_else(eqv(h, const_int(1)), const_int(2), const_int(1));
  return l;
}

int afun1()
  requires true
  ensures res::security<R> & R <= 0;
{
  return const_int(1);
}

int afun2()
  requires true
  ensures res::security<R> & R <= 1;
{
  return const_int(1);
}

int afun3(int p)
  requires p::security<R>
  ensures res::security<R> & res=p; // & R <= 0;
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
  ensures res::security<R> & R <= 1;
{
  return p;
}

int afun6(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
  return p;
}

int afun7(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 1;
{
  return p;
}

bool afun8(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
  return eqv(p, const_int(1));
}

bool afun9(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
  return lt(p, const_int(1));
}

bool afun10(int p)
  requires p::security<P> & P <= 0
  ensures res::security<R> & R <= 0;
{
  return eqv(p, const_int(1));
}

int ignore_param (int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
  int x = const_int(1);
  return x;
}

int from_param (int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
  int x = p;
  return x;
}

bool least_upper_bound1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  bool x = eqv(p, q);
  return x;
}

bool least_upper_bound2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  bool x = eqv(q, q);
  return x;
}

int assignment1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = p;
  int y = x;
  return y;
}

int assignment2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = p;
  int y = x;
  return y;
}

int assignment3 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = p;
  int y = q;
  return y;
}

int ifthen1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = if_then_else(eqv(q, const_int(0)), q, const_int(0));
  return x;
}

int ifthen2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = if_then_else(eqv(p, const_int(0)), q, const_int(0));
  return x;
}

int ifthenelse1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  x = if_then_else(eqv(q, const_int(0)), q, const_int(1));
  return x;
}

int ifthenelse2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  x = if_then_else(eqv(p, const_int(0)), q, const_int(1));
  return x;
}

int ifthenelse3 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  x = if_then_else(eqv(q, const_int(0)), q, p);
  return x;
}

int seriesif (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  int y = const_int(0);
  x = if_then_else(eqv(p, const_int(0)), const_int(1), const_int(0));
  y = if_then_else(eqv(x, const_int(0)), const_int(1), const_int(0));
  return y;
}

int nestedif1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  int y = const_int(0);
  x = if_then_else(eqv(q, const_int(0)), if_then_else(eqv(p, const_int(0)), const_int(1), const_int(0)), const_int(0));
  y = if_then_else(eqv(x, const_int(0)), const_int(1), const_int(0));
  return y;
}

int nestedif2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  int y = const_int(0);
  x = if_then_else(eqv(q, const_int(0)), if_then_else(eqv(const_int(0), const_int(0)), const_int(1), const_int(0)), const_int(0));
  y = if_then_else(eqv(x, const_int(0)), const_int(1), const_int(0));
  return y;
}

int nestedif3 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  int x = const_int(0);
  int y = const_int(0);
  x = if_then_else(eqv(q, const_int(0)), if_then_else(eqv(const_int(0), const_int(0)), const_int(1), p), const_int(0));
  y = if_then_else(eqv(x, const_int(0)), const_int(1), const_int(0));
  return y;
}

X new1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  return new X();
}

int mutation1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  x.f1 = 1;
  return x.f1;
}

int mutation2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  x.f1 = p;
  return x.f1;
}

int aliasing1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  X y = x;
  int t = 0;
  if (p != 0) {
    t = 1;
  }
  x.f1 = t;
  return x.f1;
}

int aliasing2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  X y = x;
  int t = 0;
  if (p != 0) {
    t = 1;
  }
  x.f1 = t;
  return y.f1;
}

int aliasing3 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  int t = 0;
  if (p != 0) {
    t = 1;
  }
  x.f1 = t;
  X y = x;
  return y.f1;
}

int aliasing4 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  X y = x;
  y.f1 = p;
  return y.f1;
}


int aliasing5 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  X x = new X();
  X z = new X();
  z.f1 = 0;
  int t = 0;
  if (p != 0) {
    t = 1;
  }
  x.f1 = t;
  X y = x;
  return z.f1;
}


int test (int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
  int x = 0;
  if (p != 0) {
    x = 1;
  }
  else {
    x = 2;
  }
  return x;
}
