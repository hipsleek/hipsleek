pred_prim security<i : int>;

// Currently fails with:
// Exception Failure("[context.ml]: There should be no conj/phase in the lhs at this level\n") Occurred!
int f(int h, int l)
  requires h::security<H> & l::security<L> & H <= 1 & L <= 0
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
