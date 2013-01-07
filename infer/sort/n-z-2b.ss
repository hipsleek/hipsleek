/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
//  infer [x,y]
  infer [P]
  requires y>=0 & x>=0 
    & P(x,y)
  ensures  true;

/*
Checking procedure zip$int~int... 
*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

Pre obligation is inferred below but not placed into
entail state. WHY?

 id: 4; caller: []; line: 48; classic: false; kind: PRE-2; hec_num: 2; evars: []; c_heap: emp
 checkentail emp&x=x' & y=y' & 0<=y & 0<=x & P(x,y) & x'!=0 & !(v_bool_45_511') & 
x'!=0 & !(v_bool_45_511') & y'=0 & v_bool_47_510' & y'=y' & v_bool_47_510'&
{FLOW,(22,23)=__norm}[]
 |-  hfalse&false&{FLOW,(22,23)=__norm}[]. 
res:  [
  hfalse&false&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [P]
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










