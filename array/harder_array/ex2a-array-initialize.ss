void foo(ref int[] a,int c, int i)
/*
 case {
   i>c -> ensures forall(k: a'[k]=a[k]) ;
   i<=c -> ensures forall(k: !(i<=k<=c) | a'[k]=10)
      & forall(k: (i<=k<=c) | a'[k]=a[k]) 
     ;
 }
*/
 requires i<=c+1
 ensures forall(k: !(i<=k<=c) | a'[k]=10)& 
         forall(k: (i<=k<=c) | a'[k]=a[k])
        ;

{
  if(i!=c+1){
    a[i]=10;
    foo(a,c,i+1);
  }
}

/*

 if i=c then stop
 else rec(..,i+1)

*/
