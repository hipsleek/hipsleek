global int context = 0;

data intobj {
  int val;
  int sec;
}

data boolobj {
  bool val;
  int sec;
}

intobj const_int(int i)
  requires true
  ensures res::intobj<v, R> & v = i & R<=0;

boolobj const_bool(bool b)
  requires true
  ensures res::boolobj<v, R> & v = b & R<=0;

boolobj eqv(intobj a, intobj b)
  requires a::intobj<v1, A>@L & b::intobj<v2, B>@L
  case {
    v1 = v2 -> ensures res::boolobj<true, R> & R = max(context, max(A, B));
    v1 != v2 -> ensures res::boolobj<false, R> & R = max(context, max(A, B));
  }

boolobj lt(intobj a, intobj b)
  requires a::intobj<v1, A>@L & b::intobj<v2, B>@L
  case {
    v1 < v2 -> ensures res::boolobj<true, R> & R = max(context, max(A, B));
    v1 >= v2 -> ensures res::boolobj<false, R> & R = max(context, max(A, B));
  }

boolobj not(boolobj b)
  requires b::boolobj<vb, B>
  ensures res::boolobj<v, R> & v = !vb & R = max(context, B);

intobj plus(intobj a, intobj b)
  requires a::intobj<v1, A>@L & b::intobj<v2, B>@L
  ensures res::intobj<v, R> & v = v1 + v2 & R = max(context, max(A, B));

intobj minus(intobj a, intobj b)
  requires a::intobj<v1, A>@L & b::intobj<v2, B>@L
  ensures res::intobj<v, R> & v = v1 - v2 & R = max(context, max(A, B));

intobj if_then_else(boolobj b, intobj i, intobj j)
  requires b::boolobj<vb, B>@L * i::intobj<vi, I>@L & j::intobj<vj, J>@L
  case {
    vb -> ensures res::intobj<vi, R> & R = max(max(context, B), max(I, J));
    !vb -> ensures res::intobj<vj, R> & R = max(max(context, B), max(I, J));
  }
