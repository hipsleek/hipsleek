/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P,R]
  requires x>=0 & y>=0 & P(x,y)
  ensures  R(res,x,y);

/*
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( x=v_int_46_512'+1 & y=v_int_46_511'+1 & 0<=v_int_46_512' & 
0<=v_int_46_511' & P(x,y)) -->  P(v_int_46_512',v_int_46_511'),
RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x,
RELDEFN R: ( x=0 & res=0 & 0<=y & P(x,y)) -->  R(res,x,y),
RELDEFN R: ( v_int_46_580=res-1 & v_int_46_575=x-1 & v_int_46_576=y-1 & 1<=x & 1<=y & 
P(x,y) & R(v_int_46_580,v_int_46_575,v_int_46_576)) -->  R(res,x,y)]
*************************************

!!! post_vars:[R,res,x,y]
*************************************
*******fixcalc of pure relation *******
*************************************
[( R(res,x,y), x>=0 & y>=x & res=x, P(x,y), 0<=x & x<=y)]
*************************************

!!! REL POST :  R(res,x,y)
!!! POST:  x>=0 & y>=x & res=x
!!! REL PRE :  P(x,y)
!!! PRE :  0<=x & x<=y

PROBLEM : can we gist x>=0 away
 from both pre/post

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










