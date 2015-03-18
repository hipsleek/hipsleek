int double(int n)
  infer[@post_n,@term]
  requires true
  ensures  true;
{
  if (n==0) return 0;
  else return 2+double(n-1);
}
/*
Termination Inference Result:
double:  
requires  true
  case {
    n=0 -> requires emp & Term[17,1]
           ensures true & 2*n=res & n>=0; 
   1<=n -> requires emp & Term[17,2,-1+(1* n)]
           ensures true & 2*n=res & n>=0; 
n<=(0-1) -> requires emp & Loop { 7:16}[]
            ensures false
  }

Termination Inference Result with pre n>=0

double: 
requires true 
 case {
  n=0 -> requires emp & Term[17,1]
         ensures true & 2*n=res & n>=0; 
 1<=n -> requires emp & Term[17,2,-1+(1*n)]
         ensures true & 2*n=res & n>=0; 
 n<=(0-1) -> requires emp & Loop {7:16}[]
             ensures false & false; 
 }
*/

