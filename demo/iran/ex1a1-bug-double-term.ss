int double(int n)
  requires n>=0 & Term[n]
  ensures  res=2*n & res>=0;
  requires n<0 & Loop
  ensures  false;
  infer [@term] requires true ensures true;
{
  if (n==0) return 0;
  else return 2+double(n-1);
}

/*

  requires n>=0 & Term[n]
  ensures  res=2*n & res>=0;
  requires n<0 & Loop
  ensures  false;
  infer [@term] requires true ensures true;

Why a re-verification and no inference when
it is being combined?

Checking procedure double$int... 
Procedure double$int SUCCESS.

Checking procedure double$int... 
!!! Performing a Re-verification, Valid?:trueStop Omega... 122 invocations 
4 false contexts at: ( (9,7)  (9,14)  (8,12)  (8,19) )

*/

