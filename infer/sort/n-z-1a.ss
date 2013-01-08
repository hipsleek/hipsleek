/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P]
  requires y>=0 & x>=0 & P(x,y)
  ensures  res=x;

/*


Checking procedure zip$int~int... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( y=v_int_61_512'+1 & x=v_int_61_513'+1 & 0<=v_int_61_512' & 
0<=v_int_61_513' & P(x,y)) -->  P(v_int_61_513',v_int_61_512'),
RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( true, true, true, true)]
*************************************

!!! REL POST :  true
!!! POST:  true
!!! REL PRE :  true
!!! PRE :  true

Seems incorrect.

PROBLEM:

Here, we If not need to construct top-down fix-point.


Algorithm for Pre-relation
==========================
1. gather pre obligation
2. compute fix-point of post-condition
3. form a precondition for each pre-relation
4. check if it is recursively satisfied
5. If not, derivte top-down fixpoint for pre-relation
6. compure pre-obligation tat ensures condition
   holds recursive
7. Check if it is recursively satisfied and not(false)
8. If not, inference has failed. 
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

/*
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: ( y=v_int_61_512'+1 & x=v_int_61_513'+1 & 0<=v_int_61_512' & 
0<=v_int_61_513' & P(x,y)) -->  P(v_int_61_513',v_int_61_512'),
RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]
*************************************

If we can synthesize the following formula?

wh:={[x,y]->[px,py]->[]:
  (exists (x1,y1:x>0 && y>0 && x1=x-1 && y1=y-1 && wh(x1,y1,px,py)))};
TD:=topdown(wh,1,SimHeur);
TD;

*/
