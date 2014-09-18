void loop ()
  requires Loop
  ensures false;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
    loop();
    f(x + 1);
}

/*
# loop-4b.ss

Missing cases for pre of f & post of f.

 termAssume x'=x & fpre_0(x) --> Loop.


Exception Failure("not support") Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure f$int

!!! proc.proc_name:f$int

!!! Termination Inference is not performed due to errors in verification process.


*/
