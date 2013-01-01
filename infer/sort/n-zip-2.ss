/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [R,P]
  requires x>=0 & P(x,y)
  ensures  R(res,x,y);
/*
How come below not in pure relation assumption

 inferred rel: [RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]

Checking procedure zip$int~int... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( ((v_int_57_511'=x-1 & v_int_57_510'=y-1 & y<=(0-1) & 1<=x) | 
(v_int_57_511'=x-1 & v_int_57_510'=y-1 & 1<=x & 1<=y)) & P(x,y)) -->  P(v_int_57_511',v_int_57_510'),
RELDEFN R: ( x=0 & res=0 & P(x,y)) -->  R(res,x,y),
RELDEFN R: ( ((res=v_int_57_579+1 & x=v_int_57_574+1 & y=v_int_57_575+1 & 
v_int_57_575<=(0-2) & 0<=v_int_57_574) | (res=v_int_57_579+1 & 
x=v_int_57_574+1 & y=v_int_57_575+1 & 0<=v_int_57_574 & 0<=v_int_57_575)) & 
P(x,y) & R(v_int_57_579,v_int_57_574,v_int_57_575)) -->  R(res,x,y)]
*************************************

  infer [x,y,R]
  requires x>=0 & y>=0
  ensures  R(res,x,y);

( R(res,x,y), x>=0 & y>=x & res=x)]
*************************************

!!! REL :  R(res,x,y)
!!! POST:  x>=0 & y>=x & res=x
!!! PRE :  0<=x & x<=y
Procedure zip$int~int SUCCESS


  infer [x,y,R]
  requires true
  ensures  R(res,x,y);

!!! REL :  R(res,x,y)
!!! POST:  (res>=1 & res=x) | (x=0 & res=0)
!!! PRE :  1<=x | x=0

should print below:
es_infer_pure: [(y!=0 | 0<=x) & (y!=0 | x<=0)]

[RELDEFN R: ( x=0 & res=0) -->  R(res,x,y),
RELDEFN R: ( ((res=v_int_27_576+1 & y=v_int_27_573+1 & x=v_int_27_572+1 & 
v_int_27_572<=(0-2) & v_int_27_573<=(0-2)) | (res=v_int_27_576+1 & 
y=v_int_27_573+1 & x=v_int_27_572+1 & v_int_27_573<=(0-2) & 
0<=v_int_27_572) | (res=v_int_27_576+1 & y=v_int_27_573+1 & x=v_int_27_572+
1 & v_int_27_572<=(0-2) & 0<=v_int_27_573) | (res=v_int_27_576+1 & 
y=v_int_27_573+1 & x=v_int_27_572+1 & 0<=v_int_27_573 & 0<=v_int_27_572)) & 
R(v_int_27_576,v_int_27_572,v_int_27_573)) -->  R(res,x,y)]
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










