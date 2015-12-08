data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

lemma_unsafe self::arr_seg<i,n> & i<m & m<=n 
   -> self::arr_seg<i,m>*self::arr_seg<m,n>.

arr_min_index<start,end,index> == start = end & start>=0
  or self::arr_seg_min<start,index,m> * x::arrI<m> * self::arr_seg_min<index+1,end,m> & x=self+index & start<end & start>=0
  inv start<=end & start>=0;

arr_max_index<start,end,index> == start = end & start>=0
  or self::arr_seg_max<start,index,m> * x::arrI<m> * self::arr_seg_max<index+1,end,m> & x=self+index & start<end & start>=0
  inv start<=end & start>=0;

arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2)
  inv n>i & i>=0;



/*arr_min_index<start,end,index> == start = end & start >=0
  or x::arrI<m> * arr_min_index_value<start+1,end,index,m> & start<index & index<end & start>=0;*/

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


int select_max(arrI base, int start, int end)
     requires base::arr_seg<start,end> & start<end & start>=0
     ensures base::arr_max_index<start,end,res>;
{
  if(start>=end-1){
    return start;
  }
  else{
    int t1 = get_arr(base,start);
    int pos = select_max(base,start+1,end);
    int t2 = get_arr(base,pos);
    if(t1>t2)
      {
        return start;
      }
    else
      {
        return pos;
      }
  }
}

/* void selection_sort(arrI base, int start, int end) */
/*   requires base::arr_seg<start,end> & start<end */
/*   ensures base::arr_sorted<start,end>; */
/* { */
/*   if(start>=end-1){ */
/*     return; */
/*   } */
/*   else{ */
/*     int pos = select_max(base,start,end); */
/*     int t1 = get_arr(base,pos); */
/*     int t2 = get_arr(base,start); */
/*     if(t2>t1){ */
/*       upd_arr(base,pos,t2); */
/*       upd_arr(base,pos,t1); */
/*     } */
/*     selection_sort(base,start+1,end); */
/*     return; */
/*   } */
/* } */

