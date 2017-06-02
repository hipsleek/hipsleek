pred_prim security<i : int>;

bool eqv(int a, int b)
  requires a::security<A> * b::security<B>
  case {
    a = b -> ensures res::security<R> & res & R = max(A, B);
    a != b -> ensures res::security<R> & !res & R = max(A, B);
  }

bool least_upper_bound1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 1;
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
