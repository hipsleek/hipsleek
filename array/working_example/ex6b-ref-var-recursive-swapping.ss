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
ref [k;j]
     emp&k>=k' & (5+k'+j)>=res & res=j'+k'+5&{FLOW,(4,5)=__norm#E}[]


*/

