pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

data cell { int val; }

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

/********************************************/
void foo(ref int n)
//infer[@leak]
  requires @full[n] & n>=0
  ensures @full[n] & n'=n+1;
{
  n = n+1;
}


Thrd fork_foo(ref int n)
  requires @full[n] & n>=0
  ensures res::Thrd{+ @full[n] & n'=n+1}<> ;//& n'=n;

int main(int nn)
 requires @value[nn] & nn>=0
 ensures res=nn+1;
{
  dprint;
  //State:emp*U@value[nn]&MayLoop[] & 0<=nn & nn'=nn&{FLOW,(4,5)=__norm#E}[]

  Thrd t = fork_foo(nn);
  // t_36'::Thrd{ + emp*U@full[nn]&nn'=1+nn&{FLOW,(4,5)=__norm#E}[]}<>*N
  // @full[t_36]@zero[nn]&0<=nn&{FLOW,(4,5)=__norm#E}[]
  dprint;
  join2(t);
  //State:t_36'::dead{}<>*U@full[nn,t_36]&nn'=1+nn & 0<=nn&{FLOW,(4,5)=__norm#E}[]
   dprint;
  return nn;
 }
/*
# ex13a3.ss --ann-vp (fixed)


*/
