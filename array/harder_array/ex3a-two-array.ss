void loop(ref int [] a,int i,int c,int[] b)
  requires i<=c+1
  ensures forall(k:!(i<=k<=c)|a'[k]=b[k-1]) &
          forall(k:(i<=k<=c)|a'[k]=a[k]);
{
  if(i<=c){
      a[i]=b[i-1];
      loop(a,i+1,c,b);
  }
}
