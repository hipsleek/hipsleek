pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

Thrd fork_f(ref int nnn)
  requires @full[nnn]
  ensures res::Thrd{+@full[nnn] & nnn'=nnn+1}<>;

void f(ref int nnn)
  requires @full[nnn]
  ensures @full[nnn] & nnn'=nnn+1;
 {  nnn = nnn+1;
 }

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

int main(int x)
  requires @value[x] & x=5
  ensures res=6;
{
  Thrd t = fork_f(x);
  dprint;
  join2(t);
  dprint;
  return x;
}

