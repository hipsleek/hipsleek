pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

data cell { int val; }


/********************************************/
void foo(ref int n)
 infer[@leak]
  requires @full[n]
  ensures @full[n] & n'=n+1;
{
  n = n+1;
}

/*
# ex13b.ss --ann-vp

Why this error with --classic and @leak?

Exception Failure("v_int_12_1348 does not have @full permission to write.") Occurred!



*/
