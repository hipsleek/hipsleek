data arrI{
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_pos_val<i,n,pos,v> ==
  i=n & i>=0
  or self::arr_seg<i,pos> * x::arrI<v> * self::arr_seg<pos+1,n> & x = self + pos
  inv n>=i & i>=0;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i //
  ensures res=v;

void split_arr(arrI base, int k,int i,int n)
  requires base::arr_seg<i,n>
  ensures base::arr_seg<i,k> * base::arr_seg<k,n>;

void merge_arr(arrI base,int i,int k,int n)
  requires base::arr_seg<i,k> * base::arr_seg<k,n>
  ensures base::arr_seg<i,n>;

void reverse_unfold(arrI base,int i,int n)
  requires a::arrI<_> * base::arr_seg<i+1,n> & a=base+i
  ensures base::arr_seg<i,n>;

int linear_search(arrI arr, int s, int e,int target)
  requires arr::arr_seg<s,e>
  ensures  arr::arr_seg<s,res> * x::arrI<target> * arr::arr_seg<res+1,e> & x=arr+res or res=-1;
{
  if(s>=e){
    //  assume false;
    return -1;
  }
  else{
    int tmp = get_arr(arr,s);
    if(tmp==target){
      return s; // arr[s] ==target
    }
    else{
      reverse_unfold(arr,s,e);
      split_arr(arr,s+1,s,e);
      int r = linear_search(arr,s+1,e,target);
      if(r==-1){
        return r;
      }
      else{
        merge_arr(arr,s,s+1,r);
        return r;
      }
    }
  }
}
