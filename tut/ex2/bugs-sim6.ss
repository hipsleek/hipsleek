
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
# bugs-sim6.ss

void loop(ref int n,ref int r)
  infer [P,Q]
  requires P(n,r) ensures Q(n,n',r,r');
{
  if (n==0) {

Why is there a fixcalc error?
Is it due to -(1) ??

*************************************
******pure relation assumption*******
*************************************
[RELDEFN P: ( n=0 & n'+1=0 & r+1=r' & P(n,r)) -->  P(n',r'),
RELDEFN Q: ( n=0 & Q(0-1,n',r+1,r') & P(n,r)) -->  Q(n,n',r,r'),
RELDEFN Q: ( r'=r & n'=n & n!=0 & P(n,r)) -->  Q(n,n',r,r')]
*************************************

!!!  Q(n,n',r,r') = ( r'=r & n'=n & n!=0) \/ ( n=0 & Q(0-1,n',r+1,r'))
!!! bottom up
!!! fixcalc file name: fixcalc1.inffixcalc: Parse error on line 1 rest of line: -(1),fc_r_1355,PRIn,PRIr) && fc_r_1355=r+1)))  && n=0))

!!! PROBLEM with fix-point calculation
ExceptionLoc.Exc_located(_, _)Occurred!

*/
