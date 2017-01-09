
relation P(int n,int m).
relation Q(int n,int m,int r,int p).

/*
  while (n>=0) do
  {
     n=n-1;
     r=r+1;
  }
*/

void loop(ref int n,ref int r)
  infer [P,Q]
  requires P(n,r) ensures Q(n,n',r,r');
{
  if (n==0) {
    n=n-1;
    r=r+1;
    loop(n,r);
  }
}


/*
# sim4-loop.ss

Correct result :)

Post Inference result:
loop$int~int
 EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [n;r]
           emp&((n'=0-1 & n=(r'-r)-1 & r<r') | (r=r' & n=n' & n'<=(0-1)))&
           {FLOW,(4,5)=__norm#E}[]

[RELDEFN P: ( r+1=r' & n=1+n' & 0<=(n'+1) & P(n,r)) -->  P(n',r'),
RELDEFN Q: ( 0<=(n_1352+1) & n=1+n_1352 & P(n,r) & Q(n_1352,n',1+r,r')) -->  Q(n,n',r,r'),
RELDEFN Q: ( r'=r & n=n' & (n'+1)<=0 & P(n,r)) -->  Q(n,n',r,r')]
*************************************

!!! constraints:[( r'=r & n=n' & (n'+1)<=0, Q(n,n',r,r')),( 0<=(n_1352+1) & n=1+n_1352 & Q(n_1352,n',1+r,r'), Q(n,n',r,r'))]
!!! bottom up
!!! fixcalc file name: fixcalc1.inf
!!! bottom_up_fp:[( Q(n,r,n',r'), ((n'=0-1 & n=(r'-r)-1 & r<r') | (r=r' & n=n' & n'<=(0-1))))]
!!! fixpoint:[( Q(n,r,n',r'), ((n'=0-1 & n=(r'-r)-1 & r<r') | (r=r' & n=n' & n'<=(0-1))), P(n,r), true)]
*************************************
*******fixcalc of pure relation *******
*************************************
[( Q(n,r,n',r'), ((n'=0-1 & n=(r'-r)-1 & r<r') | (r=r' & n=n' & n'<=(0-1))), P(n,r), true)]
*************************************

!!! REL POST :  Q(n,r,n',r')
!!! POST:  ((n'=0-1 & n=(r'-r)-1 & r<r') | (r=r' & n=n' & n'<=(0-1)))
!!! REL PRE :  P(n,r)
!!! PRE :  true


*/
