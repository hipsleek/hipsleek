/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P]
  requires y>=0 & x>=0 & P(x,y)
  ensures  true;

/*
Checking procedure zip$int~int... 
*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

WHY relational assumption not added below??

 id: 4; caller: []; line: 25; classic: false; kind: PRE-2; hec_num: 2; evars: []; c_heap: emp
 checkentail emp&x=x' & y=y' & 0<=y & 0<=x & P(x,y) & x'!=0 & !(v_bool_22_511') & 
x'!=0 & !(v_bool_22_511') & y'=0 & v_bool_24_510' & y'=y' & v_bool_24_510'&
{FLOW,(22,23)=__norm}[]
 |-  hfalse&false&{FLOW,(22,23)=__norm}[]. 
res:  [
  hfalse&false&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [P]
  ]

HIP and SLEEK not working consistently as shown below
in n-z-2.slk. Is this because P was being marked as 
a pre-relation?

infer [P] 
emp
& x=x' & y=y' & 0<=y & 0<=x & P(x,y) 
& x'!=0 & !(v_bool_22_518') & 
x'!=0 & !(v_bool_22_518') & y'=0 
& v_bool_24_517' & y'=y' & v_bool_24_517'
 |- false .
print residue.

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred rel: [RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]
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










