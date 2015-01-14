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
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ y!=0 | x<=0]
*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

!!! NEW SPECS: ((None,[]),EBase emp&0<=y & 0<=x&{FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=y | y<=(0-1) | x<=0) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 67::
                              
                              emp&x=0 & res=0 & 0<=y&{FLOW,(22,23)=__norm}[]
                              or emp&res=1 & 1<=y & 1<=x&
                                 {FLOW,(22,23)=__norm}[]
                              )
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
      return 1;
  }
}










