/* with virtual ptrs */


data arr_int {
  int val;
  arr_int next; /* this is virtual link */
}  inv self+1=next

/*
pred_prim arr_int<n:int,next:arr_int>
inv self+1=next;
*/

lemma_safe self::arr_seg<p,n>&n=a+b & a>=0 & b>=0 & p=self+n
  <->  (exists q: self::arr_seg<q,a>*q::arr_seg<p,b>);

arr_seg<p,n> == case {
   n=0 -> [] self=p & n=0;
   n!=0 -> [] self::arr_int<_,q>*q::arr_seg<p,n-1>;
   }
inv n>=0 &  self+n=p;
    /*
arr_seg<p,n> == self=p & n=0
  or self::arr_int<_,q>*q::arr_seg<p,n-1> & q=self+1
  inv n>=0 
  &  self+n=p;
    */

arr_seg2<p,n> == self=p & n=0
  or self::arr_int<5,q>*q::arr_seg2<p,n-1> //& q=self+1
  inv n>=0 &  self+n=p;

void upd_arr(arr_int a, int v)
  requires a::arr_int<_,q>
  ensures a::arr_int<v,q>;

arr_int arr_inc(arr_int a)
  requires a::arr_int<_,q>@L
  ensures res=q & res=a+1;

int get_arr(arr_int a)
  requires a::arr_int<v,_>@L
  ensures res=v;

void foo2(arr_int a,int i)
  requires a::arr_seg<p,n> & n=10-i+mm & i>=0 & i<=10 & mm>=0
  ensures a::arr_seg2<q,10-i> *q::arr_seg<p,mm> & q=a+(10-i)
  ;
  requires a::arr_seg<p,n> & n=10-i & i>=0 & i<=10 
  ensures a::arr_seg2<q,10-i> & q=a+(10-i) & q=p
  ;

{
  if (i<10) {
    upd_arr(a,5);
    foo2(arr_inc(a),i+1);
  }
}
