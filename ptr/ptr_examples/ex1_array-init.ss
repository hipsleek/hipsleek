
/*
array initialization
void init(ref int[] a,int i){
   if(i<10){
      a[i]=5;
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

// p is what?? Why do we need p?
arr_seg<p,n> == self=p & n=0
  or self::arr_int<_,q>*q::arr_seg<p,n-1>
  inv n>=0;

arr_seg2<p,n> == self=p & n=0
  or self::arr_int<5,q>*q::arr_seg2<p,n-1>
  inv n>=0;

arr_seg_5<p,n> == self=p & n=0
  or self::arr_int<5,q>*q::arr_seg2<p,n-1>
  inv n>=0;

arr_seg_simp<n> == self=null & n=0
  or self::arr_int<_,q> * q::arr_seg_simp<n-1>
  inv n>=0;

arr_seg_simp_2<n> == self=null & n=0
  or self::arr_int<5,q> * q::arr_seg_simp_2<n-1>
  inv n>=0;


void foo2(arr_int a,int i)
 requires a::arr_seg<p,n> & n=10-i & i>=0 & i<=10
 ensures a::arr_seg<q,10-i> *q::arr_seg<p,0>
 ;
{
  if (i<10) {
    upd_arr(a,5);
    foo2(arr_inc(a),i+1);
  }
}

void foo2(int *a,int i)
 requires a::arr_seg<p,n> & n=10-i & i>=0 & i<=10
 ensures a::arr_seg<q,10-i> *q::arr_seg<p,0>
 ;
{
  if (i<10) {
    *a=5;
    foo2(a+1,i+1);
  }
}


/*
void foo2(arr_int a,int i)
  requires a::arr_seg_simp<10-i> & i>=0 & i<=10
  ensures a::arr_seg_simp_2<10-i>
  ;
{
  if (i<10) {
    upd_arr(a,5);
    foo2(arr_inc(a),i+1);
  }
}
*/
