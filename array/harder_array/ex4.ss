void loop(ref int[] a,int i,int c,int d,int[] b)
  requires i<=c+1
  ensures forall(k:!(i<=k<=c)|a'[k] = b[d-k+i]) &
         forall(k:(i<=k<=c)|a'[k]=a[k]);
{
  if(i<=c) {
      a[i]=b[d];
      loop(a,i+1,c,d-1);
        }
}

/*

???
Post condition cannot be derived:
  (may) cause:  
i<=c & i<=(1+c) & update_array_1d(a,a_1269,a[d],i) & v_int_8_1268+1=d & 
forall(k:(!not(((1+i)<=k & k<=c)) | a'[k]=a_1269[(v_int_8_1268-k)+1+i])) & 
forall(k:(((1+i)<=k & k<=c) | a'[k]=a_1269[k])) |-  forall(k:(!not((i<=k & k<=c)) | a'[k]=a[(d-k)+i])).

*/
