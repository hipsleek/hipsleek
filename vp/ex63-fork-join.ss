pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

thrd fork(func f)<args(f)>
  requires pre(f)
  ensures  res::Thrd{post(f)}<>;

void f(ref int nnn)
  requires @full[nnn]
  ensures @full[nnn] & nnn'=nnn+1;

void join(thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

int main(int x)
  requires @value[x] & x=5
  ensures res=6;
{
  thrd t = fork(foo)<x>;
  dprint;
  join(t);
  dprint;
}

