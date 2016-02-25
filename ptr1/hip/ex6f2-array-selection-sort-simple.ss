data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

lemma_unsafe self::arr_seg<i,n> & i<m & m<=n 
   <-> self::arr_seg<i,m>*self::arr_seg<m,n>.

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2)
  inv n>i & i>=0;

arr_sorted_with_max<start,end,m> == start=end & start>=0
  or x::arrI<m> * self::arr_sorted_with_max<start+1,end,m2> & x=self+start & m>=m2 & start>=0 & start<end
  inv end>=start & start>=0;

arr_sorted<start,end> == start = end & start >=0
  or x::arrI<m> * self::arr_sorted_with_max<start+1,end,m> & start<end & start>=0
  inv start<=end & start>=0;


int get_max(arrI base,int i,int m)
 requires base::arr_seg<i,m> & i<m
 ensures base::arr_seg_max<i,m,res>;
{
  if(i<m){
    if(i==m-1)
      {
        return get_arr(base,i);
      }
    else{
      int cur = get_arr(base,i);
      int tmp = get_max(base,i+1,m);

      if(tmp<cur)
        {
          return cur;
        }
      else
        {
          return tmp;
        }
    }
  }
  else{
    return -1;
  }
}

void selection_sort(arrI base, int start, int end, arrI result)
  requires base::arr_seg<start,end> * result::arr_seg<start,end> & start<end
  ensures result::arr_sorted<start,end>;
{
  if(start>=end-1){
    return;
  }
  else{
    int value = get_max(base,start,end);
    upd_arr(result,start,value);
    selection_sort(base,start+1,end,result);
    return;
  }
}

