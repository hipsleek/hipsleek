/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P,R]
  requires y>=x & x>=0 & P(x,y)
  ensures  res=x;

/*

  requires y>=x & x>=0 
  ensures  res=x;

  infer [x,y,R]
  requires x>=0 & y>=0 
  //& P(x,y)
  ensures  R(res,x,y);

!!! REL :  R(res,x,y)
!!! POST:  x>=0 & y>=x & res=x
!!! PRE :  0<=x & x<=y

How come below not in pure relation assumption

given true
R(res,x,y) :- res=x & x>=0
pre from R :- x>=0 (is not sufficient)
==> top-down fixpoint

given x>=0 & y>=0
R(res,x,y) :- res=x & 0<=x<=y
pre from R : 0<=x<=y (is sufficient)

 inferred rel: [RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]


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










