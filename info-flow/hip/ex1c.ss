/*pred_prim security<i : int>
  inv 0 <= i & i <= 1;

data boolobj {
  bool val;
}
// b::boolobj<r> * b::security<l>

data intobj {
  int val;
}


intobj const_int(int i)
  requires true
  ensures res::intobj<v> * res::security<R> & v = i & R<=0;

boolobj const_bool(bool b)
  requires true
  ensures res::security<R> * res::boolobj<v> & b = v & R<=0;

boolobj eqv(intobj a, intobj b)
  requires a::intobj<v1>@L & b::intobj<v2>@L & a::security<A>@L & b::security<B>@L
  case {
    v1 = v2 -> ensures res::security<R> * res::boolobj<v> & v & R = max(context, max(A, B));
    v1 != v2 -> ensures res::security<R> * res::boolobj<v> & !v & R = max(context, max(A, B));
  }

boolobj lt(intobj a, intobj b)
  requires a::security<A>@L & b::security<B>@L
  case {
    a < b -> ensures res::security<R> & res & R = max(context, max(A, B));
    a >= b -> ensures res::security<R> & !res & R = max(context, max(A, B));
  }

int plus(int a, int b)
  requires a::security<A>@L & b::security<B>@L
  ensures res::security<R> & res = a + b & R = max(context, max(A, B));

int minus(int a, int b)
  requires a::security<A>@L & b::security<B>@L
  ensures res::security<R> & res = a - b & R = max(context, max(A, B));

int if_then_else(boolobj b, int i, int j)
  requires b::security<B>@L * b::boolobj<v> * i::security<I>@L & j::security<J>@L
  case {
    v -> ensures res = i & I = max(max(context, B), max(I, J));
    !v -> ensures res = j & J = max(max(context, B), max(I, J));
  }

global int context = 0;*/

hip_include 'ex2.ss'

intobj f(intobj h, intobj l)
  requires h::intobj<vh, H> * l::intobj<vl, L> & H <= 1 & L <= 0
  ensures res::intobj<v, R> & R <= 0;
{
  context = 1;
  l = if_then_else(eqv(h, const_int(1)) , const_int(2), const_int(1));
  context = 0;
  return l;
}
