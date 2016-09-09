/* with virtual ptrs */

data arr_int {
  int val;
  arr_int next; //(* this is virtual link *)
}  inv self+1=next // Don't put semicolon here.

arr_seg<p,n> == self=p & n=0
  or self::arr_int<_,q>*q::arr_seg<p,n-1>
  inv n>=0  &  self+n=p;

lemma_safe self::arr_seg<p,n> & n=a+b & a>=0 & b>=0 <->
  (exists q: self::arr_seg<q,a> * q::arr_seg<p,b>);

void upd_arr(arr_int a, int v)
  requires a::arr_int<_,q>
  ensures a::arr_int<v,q>;

arr_int arr_inc(arr_int a)
  requires a::arr_int<_,q>@L
  ensures res=q;

int get_arr(arr_int a)
  requires a::arr_int<v,_>@L
  ensures res=v;

arr_int arr_add(arr_int a, int i)
  requires a::arr_int<v,_>@L & i>=0
  ensures res=a+i;

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

/*


x::arr<i,v>


void foo2(int[] a,int i)
{
    if(i<10){
      a[i]=5;==>*(a+i)=5;
      foo2(a,i+1);
    }
}

==>

data arr_int{
int val;
}

arr_seg<n,l> ==
cur::arr_int<_> * q::arr_seg<n+1,l> & q=self+1 & cur=self+n;

void upd_arr(arr_int a,int i,int v)
requires a::arr_seg<i,l>
ensures a::arr_seg2<i,l>



*/
