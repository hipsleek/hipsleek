//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a).
relation Q(int a,int r).

int foo(int a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [P,Q] requires P(a) ensures Q(res,a);
{
  if (a>10) {
    return a;
  } else {
    assume false;
    return -1;
  }
}

/*
# ex11a1.ss

Should fail when there is a type error;
unless we have ignore-type-error flag.

[RELDEFN Q: ( a=res & 11<=res & P(a)) -->  Q(res,a)]

Post Inference result:
foo$int
 EBase emp&11<=a & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&a=res & 11<=res&{FLOW,(4,5)=__norm#E}[]
           


 */
