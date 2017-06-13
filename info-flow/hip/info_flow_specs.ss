global int context = 0;

int const_int(int i)
  requires true
  ensures res::security<R> & res=i & R<=0;

bool const_bool(bool b)
  requires true
  ensures res::security<R> & res=b & R<=0;

bool eqv(int a, int b)
  requires a::security<A>@L & b::security<B>@L
  case {
    a = b -> ensures res::security<R> & res & R = max(context, max(A, B));
    a != b -> ensures res::security<R> & !res & R = max(context, max(A, B));
  }

bool lt(int a, int b)
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

int if_then_else(bool b, int i, int j)
  requires b::security<B>@L * i::security<I>@L & j::security<J>@L
  case {
    b -> ensures res::security<R> & res = i & R = max(max(context, B), max(I, J));
    !b -> ensures res::security<R> & res = j & R = max(max(context, B), max(I, J));
  }
