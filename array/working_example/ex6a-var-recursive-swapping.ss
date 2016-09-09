relation P(int[] a).
  relation Q(int i,int j,int ip,int jp,int r).

  int foo(ref int k,ref int j)
  infer [Q] requires true ensures Q(k,j,k',j',res);
{
   if(k>0){
      k = k-1;
      return foo(j,k);
   }
   else{
     return j+k+5;
   }

}


/*

emp&((k>=1 & j>=k & j+5=res+k) | (j>=1 & k>=(1+j) & k+4=res+j) | 
     (0>=j & k>=1 & j+k+4=res) | (0>=k & j+k+5=res))&{FLOW,(4,5)=__norm#E}[]


*/

