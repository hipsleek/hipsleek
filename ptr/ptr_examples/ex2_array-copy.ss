
/*
array copy
void copy(ref int[] a,int[] b,int i){
   if(i<10){
      a[i]=b[i+k];
      init(a,i+1);
   }
}
*/
data arr_int {
  int val;
  arr_int next;
}

void upd_arr(arr_int a, int v)
  requires a::arr_int<_,q>
  ensures a::arr_int<v,q>;

arr_int arr_inc(arr_int a)
  requires a::arr_int<_,q>@L
  ensures res=q;

int get_arr(arr_int a)
  requires a::arr_int<v,_>@L
  ensures res=v;

arr_seg<p,n> == self=p & n=0
  or self::arr_int<_,q>*q::arr_seg<p,n-1>
  inv n>=0;

arr_seg2<p,n> == self=p & n=0
  or self::arr_int<5,q>*q::arr_seg2<p,n-1>
  inv n>=0;


arr_seg_copy<b,p,n> == self=p & n=0
  or self::arr_int<v,q>*b::arr_int<v,qb>*q::arr_seg_copy<qb,p,n-1>
  inv n>=0;

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


