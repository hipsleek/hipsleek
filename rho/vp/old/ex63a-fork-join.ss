pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

thrd fork_f(ref int nnn)
  requires @full[nnn]
  ensures  res::Thrd{+@full[nnn] & nnn'=nnn+1}<>;//'

void f(ref int nnn)
  requires @full[nnn]
  ensures @full[nnn] & nnn'=nnn+1;

void join_2(thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

int main(int x)
  requires @value[x] & x=5
  ensures res=6;
{
  dprint;
  // @value[x]&MayLoop[] & x=5 & x'=x
  thrd t = fork_f(x);
  //t_38'::Thrd{ + emp*N@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]}<>*N@full[t_38]@zero[x]&x=5
  dprint;
  join_2(t);
  /* 
   t_38'::dead{}<>*N@full[t_38,x]&x'=1+x & x=5
   [Q --> emp*N@full[x]&x'=1+x}
  */
  dprint;
  return x;
}

