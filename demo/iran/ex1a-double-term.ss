
int double(int n)
/*
  requires n>=0 & Term[n]
  ensures  res=2*n+1 & res>=0;
  requires n<0 & Loop
  ensures  false;
*/
  infer [@post_n,@term] requires true ensures true;
{
  if (n==0) return 0;
  else return 2+double(n-1);
}


/*
//infer [@term] requires true ensures true;

double:  
 requires true 
 case {
   n=0 -> 
     requires emp & Term[17,1]
     ensures true & true;
  1<=n -> 
     requires emp & Term[17,2,-1+(1*n)]
     ensures true & true; 
 n<=(0-1) -> 
     requires emp & Loop{11:16}[]
     ensures false ; 
 }
*/

