data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

lemma_unsafe self::arr_seg<i,n> & i<m & m<=n 
   -> self::arr_seg<i,m>*self::arr_seg<m,n>.


arr_seg_sorted<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0
  or x::arrI<mi>*self::arr_seg_sorted<i+1,n,m2> & x=self+i 
       & i>=0 & i<n-1 & mi<=m2
  inv n>i & i>=0;

arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2)
  inv n>i & i>=0;


arr_seg_min<i,n,minv> == x::arrI<minv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_min<i+1,n,minv2> & x=self+i & i>=0 & i<n-1 & minv=min(cur,minv2)
  inv n>i & i>=0;


void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;
  //
int partition(arrI base,int start,int end,int pivot)
     requires base::arr_seg<start,end> & start<=end & start>=0
     ensures base::arr_seg_max<start,res,maxv> * base::arr_seg_min<res+1,end,pivot> & maxv<pivot ;
{

  if(start>=end){
    return start;
  }
  else{
    if(get_arr(base,start)<pivot){
      return partition(base,start+1,end,pivot);
    }
    else{
      if(get_arr(base,end)>=pivot){
        return partition(base,start,end-1,pivot);
      }
      else{
        int t;
        t = get_arr(base,start);
        upd_arr(base,start,get_arr(base,end));
        upd_arr(base,end,t);
        return partition(base,start+1,end,pivot);
      }
    }
  }
}

/* void quick_sort(arrI base, int start, int end){ */
/*   if(start>=end){ */
/*     return; */
/*   } */
/*   else{ */
/*     int pivot = get_arr(base,start); */
/*     int p = partition(base,start,end,pivot); */
/*     quick_sort(base,start,p); */
/*     quick_sort(base,p,end); */
/*   } */
/* } */
