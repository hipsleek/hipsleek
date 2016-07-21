

void loop(ref int i, int n)
   requires true
   ensures true;
{
  while (i!=0)
  case {
    i>=0 -> requires  Term[i] 
            ensures  n'-n=2*(i-i') & i'=0;
    i<0 -> requires Loop 
    ensures  false;
 }
  {
    i=i-1; n=n+2;
  }

}
