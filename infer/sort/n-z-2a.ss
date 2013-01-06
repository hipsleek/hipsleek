/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [x,y]
  requires y>=0 & x>=0 
  ensures  true;

/*
Checking procedure zip$int~int... 
*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

Procedure zip$int~int SUCCESS

Pure is inferred below but disappeared in the
end. This may be due to our use of false elimination
to reduce the contexts.

 id: 4; caller: []; line: 29; classic: false; kind: PRE-2; hec_num: 2; evars: []; c_heap: emp
 checkentail emp&x=x' & y=y' & 0<=y & 0<=x & x'!=0 & !(v_bool_26_511') & x'!=0 & 
!(v_bool_26_511') & y'=0 & v_bool_28_510' & y'=y' & v_bool_28_510'&
{FLOW,(22,23)=__norm}[]
 |-  hfalse&false&{FLOW,(22,23)=__norm}[]. 
res:  [
  hfalse&false&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [x; y]
  es_infer_pure: [y!=0 | x<=0]
  ]

*/

{
  if (x==0) return 0;
  else {
    if (y==0) {
       error();
       return -1;
    }
    else 
      return 1;
  }
}










