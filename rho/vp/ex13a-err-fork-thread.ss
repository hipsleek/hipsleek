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
 ensures res=nn+1;
{
  Thrd t = fork_foo(nn);
  //int r = nn;
  //Exception Failure("nn does not have @lend/@full permission to read (var access)") Occurred!
  dprint;
  join2(t);
  dprint;
  return nn;
 }
/*
# vp/ex13a.ss --ann-vp

Why this error with --classic and @leak?

Exception Failure("v_int_12_1348 does not have @full permission to write.") Occurred!



*/
