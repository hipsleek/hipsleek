
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

void bubble(arr_int a, int i, int j){
  bool res;
  res = bubble_helper(a,i,j);
  if(b){
    bubble(a,i,j);
  }
}

bool bubble_helper(arr_int a, int i, int j){
  if(i+1==j)
    return false;
  else{
    bool flag;
    if(get_arr(a)<=get_arr(arr_inc(a))){
      flag = false;
    }
    else{
      int aux;
      aux = get_arr(a);
      upd_arr(a,get_arr(arr_inc(a)));
      upd_arr(arr_inc(a),aux);
      flag = true;
    }
    bool flag_new = bubble_helper(a,i+1,j);
    return (flag_new||flag);
  }
}



/*
void copy(arr_int a,arr_int b,int i)
  requires a::arr_seg<p,n> & n=10-i+5 & i>=0 & i<=10
  ensures a::arr_seg_copy<b,q,10-i> *q::arr_seg<p,5>
  ;
{
  if (i<10) {
    upd_arr(a,get_arr(b));
    foo2(arr_inc(a),i+1);
  }
}
*/

