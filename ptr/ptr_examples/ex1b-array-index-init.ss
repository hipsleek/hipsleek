/*
 data arr_int {
  int val;
  arr_int next;
}

data arr_int2 {
  int offset;
  int val;
}
*/

data arr_int3 {
  int val;
}

/*
pred_prim arr2<v:int> ;

void upd_arr(arr_int a, int v)
  requires a::arr_int<_,q>
  ensures a::arr_int<v,q>;

arr_int arr_inc(arr_int a)
  requires a::arr_int<_,q>@L
  ensures res=q;

int get_arr(arr_int a)
  requires a::arr_int<v,_>@L
  ensures res=v;
*/

void update_arr(arr_int2 a,int i,int v)
  requires a+i::arr_int3<_>
  ensures  a+i::arr_int3<v>;

arr_seg<i,n> == emp & i>=n
  or self+i::arr_int3<_> * self::arr_seg<i+1,n>
  inv n>=0;

arr_seg2<i,n> == emp & i>=n
  or self+i::arr_int3<5> * self::arr_seg2<i+1,n>
  inv n>=0;

void foo2(arr_int2 a,int i)
  requires a::arr_seg<i,10> & i<=10
  ensures a::arr_seg2<i,10>
{
  if (i<10) {
    update_arr(a,i,5); // a[i] = 5;
    foo2(a,i+1);
  }
}


