/* without virtual ptrs */

data arr_int {
  int val;
}

arr_seg<p,n> == self=p & n=0
  or self::arr_int<_>*q::arr_seg<p,n-1> & q=self+1
  inv n>=0 & p=self+n;

lemma_safe self::arr_seg<p,n> & n=a+b & a>=0 & b>=0 
      <->
  (exists q: self::arr_seg<q,a> * q::arr_seg<p,b>);

void upd_arr(arr_int a, int v)
  requires a::arr_int<_>
  ensures a::arr_int<v>;

arr_int arr_inc(arr_int a)
  requires a::arr_int<_>@L
  ensures res=a+1;

int get_arr(arr_int a)
  requires a::arr_int<v>@L
  ensures res=v;

arr_int arr_add(arr_int a, int i)
  requires a::arr_int<v>@L
  ensures res=a+i;

/*
arr_seg2<p,n> == self=p & n=0
  or self::arr_int<5,q>*q::arr_seg2<p,n-1>
  inv n>=0;

void foo2(arr_int a,int i)
  requires a::arr_seg<p,n> & n=10-i+5 & i>=0 & i<=10
  ensures a::arr_seg2<q,10-i> *q::arr_seg<p,5>
  ;
{
  if (i<10) {
    upd_arr(a,5);
    foo2(arr_inc(a),i+1);
  }
}
*/
