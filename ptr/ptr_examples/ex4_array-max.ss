
/*
array copy
void copy(ref int[] a,int[] b,int i){
   if(i<10){
      a[i]=b[i+k];
      init(a,i+1);
   }
}
*/
/*
arr_seg_copy<b,p,n> == self=p & n=0
  or self::arr_int<v,q>*b::arr_int<v,qb>*q::arr_seg_copy<qb,p,n-1>
  inv n>=0;
*/



void array_max(arr_int a,arr_int b,ref int m)
{
  if (i<10) {
    if (m<get_arr(a))
      m = get_arr(a);
    array_max(arr_inc(a),i+1);
  }
}


