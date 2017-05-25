global int h;
global int l;

pred_prim security<i : int>;

// Should fail, but doesn't
void f()
  requires h::security<H> & l::security<L> & H <= 1 & L <= 0
  ensures H <= 1 & L <= 0;
{
  if (h == 1) {
    l = 2;
  }
  else {
    l = 1;
  }
}
