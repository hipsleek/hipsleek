/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P,R]
  requires x>=0 & P(x,y)
  ensures  R(res,x,y);

/*
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( ((v_int_46_511'=x-1 & v_int_46_510'=y-1 & y<=(0-1) & 1<=x) | 
(v_int_46_511'=x-1 & v_int_46_510'=y-1 & 1<=x & 1<=y)) & P(x,y)) -->  P(v_int_46_511',v_int_46_510'),
RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x,
RELDEFN R: ( x=0 & res=0 & P(x,y)) -->  R(res,x,y),
RELDEFN R: ( ((res=v_int_46_579+1 & x=v_int_46_574+1 & y=v_int_46_575+1 & 
v_int_46_575<=(0-2) & 0<=v_int_46_574) | (res=v_int_46_579+1 & 
x=v_int_46_574+1 & y=v_int_46_575+1 & 0<=v_int_46_574 & 0<=v_int_46_575)) & 
P(x,y) & R(v_int_46_579,v_int_46_574,v_int_46_575)) -->  R(res,x,y)]
*************************************

!!! post_vars:[R,res,x,y]
*************************************
*******fixcalc of pure relation *******
*************************************
[( R(res,x,y), (res>=1 & res=x) | (x=0 & res=0), P(x,y), (y<=(0-1) & 1<=x) | (1<=x & x<=y) | x=0)]
*************************************

!!! REL POST :  R(res,x,y)
!!! POST:  res=x & 0<=x
!!! REL PRE :  P(x,y)
!!! PRE :  y<=(0-1) | (x<=y & 1<=y) | (x=0 & 0<=y)
Procedure zip$int~int SUCCESS

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










