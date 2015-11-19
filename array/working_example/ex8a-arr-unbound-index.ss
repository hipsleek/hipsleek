relation P(int[] a).
  relation Q(int[] a,int[] b,int i,int ip).

  void foo(ref int[] arr,ref int i)
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(arr,arr',i,i');
{
   if(i<10){
      arr[i] = 0;
      i = i+1;
      foo(arr,i);
      return;
   }
   else{
     return;
   }

}
