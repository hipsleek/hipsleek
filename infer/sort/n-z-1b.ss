/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P]
  requires x>=0 & P(x,y)
  ensures  res=x;

/*

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( ((v_int_58_512'=x-1 & v_int_58_511'=y-1 & y<=(0-1) & 1<=x) | 
(v_int_58_512'=x-1 & v_int_58_511'=y-1 & 1<=x & 1<=y)) & P(x,y)) -->  P(v_int_58_512',v_int_58_511'),
RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( true, true, P(x,y), (y<=(x-1) & y<=(0-1)) | x<=y)]
*************************************

!!! REL POST :  true
!!! POST:  true
!!! REL PRE :  P(x,y)
!!! PRE :  (y<=(x-1) & y<=(0-1)) | x<=y
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

