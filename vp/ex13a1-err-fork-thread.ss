pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

data cell { int val; }

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

/********************************************/
void foo(ref int n)
//infer[@leak]
  requires @full[n]
  ensures @full[n] & n'=n+1;
{
  n = n+1;
}


Thrd fork_foo(ref int n)
  requires @full[n]
  ensures res::Thrd{+ @full[n] & n'=n+1}<> ;//& n'=n;

int main(int nn)
 requires @value[nn]
 ensures res=1;
{
  nn=0;
  dprint;
  Thrd t = fork_foo(nn);
  //t_36'::Thrd{ + emp*U@full[nn]&nn'=1+nn&{FLOW,(4,5)=__norm#E}[]}<>*N@full[t_36]@zero[nn]&nn_1403=nn&{FLOW,(4,5)=__norm#E}[]
  //what happen to nn=0?
  dprint;
  join2(t);
  dprint;
  return nn;
 }
/*
# ex13a.ss --ann-vp

Why this error with --classic and @leak?

Exception Failure("v_int_12_1348 does not have @full permission to write.") Occurred!



*/
