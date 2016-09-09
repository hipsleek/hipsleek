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

/* arr_seg_sorted<i,n,v> == i=n & i>=0 */
/*   or self::arrI<v> * self::arr_seg_sorted<i+1,n,v1>  */

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
  requires base::arr_seg<i,n> & k>=i & k<=n
  ensures base::arr_seg<i,k> * base::arr_seg<k,n>;

void merge_arr(arrI base,int i,int k,int n)
  requires base::arr_seg<i,k> * base::arr_seg<k,n>
  ensures base::arr_seg<i,n>;

void reverse_unfold(arrI base,int i,int n)
  requires a::arrI<_> * base::arr_seg<i+1,n> & a=base+i
  ensures base::arr_seg<i,n>;

void merge_arrI_with_seg_tail(arrI base,int i,int n)
  requires base::arr_seg<i,n> * x::arrI<_> & x=base+n
  ensures base::arr_seg<i,n+1>;

int get_arr_special(arrI base, int i)
  requires true
  ensures true;

int get_pos(int s, int e)
  requires s<e
  ensures res = (s+e)/2 & res>=s & res<e;

int binary_search(arrI arr, int s, int e,int target)
  requires arr::arr_seg<s,e>
  ensures  arr::arr_seg<s,res> * x::arrI<target> & x=arr+res or res=-1;
{
  if(s>=e){
    //  assume false;
    return -1;
  }
  else{
    int pos = (s+e)/2;
    split_arr(arr,pos,s,e);
    int tmp = get_arr(arr,pos);
    if(tmp==target){
      return pos; // arr[s] ==target
    }
    else{
      int r;
      if(tmp<target){
        merge_arrI_with_seg_tail(arr,s,pos);
        r = binary_search(arr,pos+1,e,target);
        if(r==-1){
          return r;
        }
        else{
          merge_arr(arr,s,pos+1,r);
          return r;
        }
      }
      else{
        r = binary_search(arr,s,pos,target);
      }
      return r;
    }
  }
}
