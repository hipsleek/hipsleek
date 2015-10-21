
data arr_int2 {
  int val;
}

/*
data arr_int3 {
  int offset;
  int val;
} inv {self+i}
*/

pred arr_int<o:int,v:int> ==
    p::arr_int2<v> & p=self+1;

/*

void update_arr(arr_int2 a,int i,int v)
  requires a::arr_int<i,_>
  ensures  a::arr_int<i,v>;

arr_seg<i:int,n:int> == emp & i>=n
  or self::arr_int<i,_> * self::arr_seg<i+1,n>
  inv n>=0;

arr_seg2<i:int,n:int> == emp & i>=n
  or self::arr_int<i,5> * self::arr_seg2<i+1,n>
  inv n>=0;

void foo2(arr_int2 a,int i)
  requires a::arr_seg<i,10> & i<=10
  ensures a::arr_seg2<i,10>;
{
  if (i<10) {
    update_arr(a,i,5); // a[i] = 5;
    foo2(a,i+1);
  }
}

*/
