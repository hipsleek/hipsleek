//hip_include '../prelude_aux.ss'
//#option --ato
relation Q(int a,int b,int r).

int foo(ref int a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  if (a>0) {
    // a[6] = a[6]+1;
    a = a-1;
    return foo(a); } 
  else {
    int tmp=a;
    return tmp;
  }
}

/*
# ex13b.ss 

!!! fixcalc file name: logs/fixcalc.inf
(==fixcalc.ml#193==)
parse_fix@1
parse_fix inp1 :a >= 1 && 0 = PRIa && 0 = res || 0 >= res && res = a && res = PRIa


parse_fix@1 EXIT:[ ((a:int>=1 & 0=a#':int & 0=res:int) | (!(res:int) & res:int=a:int & 
res:int=a#':int))]

 
*/
