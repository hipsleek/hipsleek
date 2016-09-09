data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

/*arr_seg_sorted<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0
  or x::arrI<mi>*self::arr_seg_sorted<i+1,n,m2> & x=self+i 
       & i>=0 & i<n-1 & mi<=m2
  inv n>i & i>=0;
*/

/*
arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2)
  inv n>i & i>=0;
*/

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

arr_seg_min<start,end,m> == start = end & start >=0
  or x::arrI<cur> * self::arr_seg_min<start+1,end,min2> & x = self+start & m = min(cur,min2) & start<end & start>=0
  inv start<=end & start>=0;

arr_seg_min_head<start,end> == start = end & start >= 0
  or x::arrI<m> * self::arr_seg_min<start+1,end,m> & x=self+start & start<end & start>=0
  inv end>=start & start>=0;

arr_sorted_with_min<start,end,m> == start=end & start>=0
  or x::arrI<m> * self::arr_sorted_with_min<start+1,end,m2> & x=self+start & m<m2 & start>=0 & start<end
  inv end>=start & start>=0;

arr_sorted<start,end> == start = end & start >=0
  or x::arrI<m> * self::arr_sorted_with_min<start+1,end,m> & start<end & start>=0
  inv start<=end & start>=0;

lemma_unsafe self::arr_seg<i,n> & i<=m & m<=n 
   <-> self::arr_seg<i,m>*self::arr_seg<m,n>.

arr_bseg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_bseg<i,n-1> & x=self+(n-1) & i>=0
  inv n>=i & i>=0;

void bubble_push(arrI base, int start, int end)
 case {
  start=end -> ensures emp;
  start!=end -> 
    requires base::arr_seg<start,end>
    ensures  base::arr_seg<start,end-1>*r::arrI<m>&r=base+(end-1);
}
 //ensures base::arr_seg_min_head<start,end>;
{
  if(start>=end-1){
    //dprint;
    return;
  }
  else{
    //assume false;
    int e1 = get_arr(base,start);
    int e2 = get_arr(base,start+1);
    if(e1<e2){
      upd_arr(base,start,e2);
      upd_arr(base,start+1,e1);
      bubble_push(base, start+1, end);
    }
    else{
      bubble_push(base,start+1,end);
    }
  }
}

/*
void bubble_sort(arrI base, int start, int end)
  requires base::arr_seg<start,end> & start<end
  ensures base::arr_sorted<start,end>;
{
  if(start>=end-1){
    return;
  }
  else{
    bubble_push(base,start,end);
    bubble_sort(base,start+1,end);
    return;
  }
}
*/
