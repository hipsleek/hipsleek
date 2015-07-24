//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
infer [@arrvar,P] requires true ensures P(res,a[5]);
//  infer [@arrvar,P] requires true ensures P(res,a[4]);
{
  return a[5];
}

/*

infer [@arrvar,P] requires true ensures P(res,a[5]);

Post Inference result:
foo$int[]
 EBase htrue&exists(res:exists(a:a[5]=res)) & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&a[5]=res&{FLOW,(4,5)=__norm#E}[]

 */
