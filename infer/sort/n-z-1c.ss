/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P]
  requires P(x,y)
  ensures  res=x;

/*

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( ((v_int_47_510'=y-1 & v_int_47_511'=x-1 & y<=(0-1) & x<=(0-1)) | 
(v_int_47_510'=y-1 & v_int_47_511'=x-1 & y<=(0-1) & 1<=x) | (v_int_47_510'=y-
1 & v_int_47_511'=x-1 & x<=(0-1) & 1<=y) | (v_int_47_510'=y-1 & 
v_int_47_511'=x-1 & 1<=y & 1<=x)) & P(x,y)) -->  P(v_int_47_511',v_int_47_510'),
RELASS [P]: ( P(x,y)) -->  (y!=0 | 1>x) & (y!=0 | x>(0-1))]
*************************************

PROBLEM 1 : why wasn't P1 :={[x,y]: y!=0 | x=0}; 
used instead or even:
  PairWiseCheck P2;
  // x=0 | y<=-1 | y>=1
  // {[0,y]} union {[x,y]: y <= -1} union {[x,y]: 1 <= y}


PROBLEM 2: It seems like there is a big disjunction:

[RELDEFN P: ( 
((v_int_51_510'=y-1 & v_int_51_511'=x-1 & y<=(0-1) & x<=(0-1)) | 
(v_int_51_510'=y-1 & v_int_51_511'=x-1 & y<=(0-1) & 1<=x) 
| (v_int_51_510'=y-1 & v_int_51_511'=x-1 & x<=(0-1) & 1<=y) 
| (v_int_51_510'=y-1 & v_int_51_511'=x-1 & 1<=y & 1<=x)) & P(x,y)) 
-->  P(v_int_51_511',v_int_51_510'),
directive.

This caused the default pre-cond generated with fixclac-disj=2
to be too strong

If we use -fixcalc-disj of 4 to get sufficient precision for
this example due to the presence of double !=0.

  {[x,y]: x=0 & 0 <= y or x <= y && 1 <= y or y <= -1

For example -fixcalc-disj 4 gave the following
result:

!!! PRE :  (0<=x & x<=y) | y<=(0-1)

*/
{
  if (x==0) return 0;
  else {
    if (y==0) {
       error();
       return -1;
    }
    else 
      return 1+zip(x-1,y-1);
  }
}

