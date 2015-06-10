void loop(ref int [] a,int i,int c)
  requires i<=c+1
  ensures forall(k:!(i<=k<=c)|a'[k]=a[k-1]) &
          forall(k:(i<=k<=c)|a'[k]=a[k]);
{
  if(i<=c){
      a[i]=a[i-1];
      loop(a,i+1,c);
  }
}
