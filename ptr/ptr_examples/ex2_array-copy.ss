
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

arr_seg1<p,f,n> == self=p & n=0
  or self::arr_int<v,q>*q::arr_seg1<p,f,n-1> & f[n]=v
  inv n>=0;

arr_seg2<p,n> == self=p & n=0
  or self::arr_int<5,q>*q::arr_seg2<p,n-1>
  inv n>=0;

arr_seg_copy<b,p,n> == self=p & n=0
  or self::arr_int<v,q>*b::arr_int<v,qb>*q::arr_seg_copy<qb,p,n-1>
  inv n>=0;

arr_seg_simp<n> == self=null & n=0
  or self::arr_int<_,p> * p::arr_seg_simp<n-1>
  inv n>=0;

arr_seg_simp_v<n,v> == self=null & n=0
  or self::arr_int<v,p> * p::arr_seg_simp_v<n-1,v>
  inv n>=0;

void copy(arr_int a,arr_int b,int i)
/*
  requires a::arr_seg<p,n> & n=10-i+5 & i>=0 & i<=10
  ensures a::arr_seg_copy<b,q,10-i> *q::arr_seg<p,5>;
  requires a::arr_seg1<p,g,n> * b::arr_seg1<p,f,n> & n=10-i+5 & i>=0 & i<=10
  ensures a::arr_seg1<q,f,10-i> *q::arr_seg<p,g,5>;
*/

// Why we cannot add @L for b???
  requires a::arr_seg_simp<10-i> * b::arr_seg_simp_v<10-i,v> & i>=0 & i<=10
  ensures a::arr_seg_simp_v<10-i,v> * b::arr_seg_simp<10-i>;

{
  if (i<10) {
    upd_arr(a,get_arr(b));
    copy(arr_inc(a),arr_inc(b),i+1);
  }
}

arr_seg_index<index,length> == self=null & length=0
  or self::arr_int<_,p> * p::arr_seg_index<index+1,length-1>
  inv length>=0;

arr_seg_index_value<index,length,f> == self=null & length=0
  or self::arr_int<v,p> * p::arr_seg_index_value<index+1,length-1,f> & f[index]=v
  inv length>=0;


void copy2(arr_int a,arr_int b,int i)
  requires a::arr_seg_index<i,10-i> * b::arr_seg_index_value<i,10-i,f> & i>=0 & i<=10
  ensures a::arr_seg_index_value<i,10-i,f> * b::arr_seg_index_value<i,10-i,f>;

{
  if (i<10) {
    upd_arr(a,get_arr(b));
    copy2(arr_inc(a),arr_inc(b),i+1);
  }
}


arr_seg_index_p<index,length,end> == self=end & length=0
  or self::arr_int<_,p> * p::arr_seg_index_p<index+1,length-1,end>
  inv length>=0;

arr_seg_index_value_p<index,length,f,end> == self=end & length=0
  or self::arr_int<v,p> * p::arr_seg_index_value_p<index+1,length-1,f,end>
  & f[index]=v
  inv length>=0;


void copy3(arr_int a,arr_int b,int i)
  requires a::arr_seg_index_p<i,10-i,end_a> * b::arr_seg_index_value_p<i,10-i,f,end_b> & i>=0 & i<=10
  ensures a::arr_seg_index_value_p<i,10-i,f,end_a> * b::arr_seg_index_value_p<i,10-i,f,end_b>;

{
  if (i<10) {
    upd_arr(a,get_arr(b));
    copy3(arr_inc(a),arr_inc(b),i+1);
  }
}

void copy3(arr_int a,arr_int b,int i)
{
  if (i<10) {
    *a = *b;
    copy3(a++,b++,i+1);
  }
}





