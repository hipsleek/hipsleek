data arrI {
  int val;
}

// Predicates
arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_sorted<i,n,mi> == x::arrI<v> & x=self+i & i=n-1 & i>=0 & v<=mi
  or x::arrI<v>*self::arr_seg_sorted<i+1,n,m2> & x=self+i & i>=0 & i<n-1 & v<=mi & mi>=m2 & v>=m2
  inv n>i & i>=0;

arr_seg_max_2<i,n,maxv> == i=n & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max_2<i+1,n,maxv2> & x=self+i & i>=0 & i<n & ((!(i=n-1))|maxv=cur) & maxv=max(cur,maxv2)
  inv n>=i & i>=0;

/* arr_seg_max_min<i,n,ma,mi> == i=n & i>=0 */
/*   or x::arrI<cur> * self::arr_seg_max_min<i+1,n,ma1,mi1> & x=self+i & i>=0 & i<n & ((!(i=n-1))|(ma=cur&mi=cur)) & ma=max(cur,ma1) & mi=min(cur,mi1) */
/*   inv n>=i & i>=0; */

arr_seg_max_min<i,n,ma,mi> == i=n & i>=0
  or x::arrI<cur> * self::arr_seg_max_min<i+1,n,ma,mi> & x=self+i & i>=0 & i<n & cur<=ma & cur>mi
  inv n>=i & i>=0;

// Primitive operations

void split_arr(arrI base, int i, int n, int k)
  requires base::arr_seg<i,n> & k>=i & k<=n
  ensures base::arr_seg<i,k> * base::arr_seg<k,n>;

void unfold_tail(arrI base, int i, int n)
  requires base::arr_seg<i,n> & i<n
  ensures base::arr_seg<i,n-1> * x::arrI<v> & x+1= base+n;

void reverse_unfold(arrI base, int i,int n)
 case{
  i<n -> requires x::arrI<v>*base::arr_seg<i+1,n> & x=base+i
    ensures base::arr_seg<i,n>;
  i>=n -> requires true
    ensures true;
}

void reverse_unfold_2(arrI base, int i,int n)
  requires x::arrI<v>*base::arr_seg_max_min<i+1,n,ma,mi> & x=base+i
  ensures base::arr_seg_max_min<i,n,max(v,ma),min(v,mi)>;

void reverse_unfold_tail(arrI base, int i,int n)
 case{
  i<n -> requires x::arrI<v>*base::arr_seg<i,n-1> & x+1=base+n
    ensures base::arr_seg<i,n>;
  i>=n -> requires true
    ensures true;
}

void reverse_unfold_tail_2(arrI base, int i,int n)
 case{
  i<n -> requires x::arrI<v>*base::arr_seg_max_min<i,n-1,ma,mi> & x+1=base+n
    ensures base::arr_seg_max_min<i,n,max(v,ma),min(v,mi)>;
  i>=n -> requires true
    ensures true;
}


void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v> & a=base+i;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;


// Shape verification working
int partition(arrI base, int i, int m, int pivot)
  requires base::arr_seg<i,m>
  ensures base::arr_seg_max_min<i,res,pivot1,_> * base::arr_seg_max_min<res,m,_,pivot2> & pivot1<=pivot & pivot2>=pivot;
{
  if(i==m){
    //    assume false;
    return i;
  }
  else{
    if(i<m-1){
      //assume false;
      unfold_tail(base,i,m);
      int tmpi=get_arr(base,i);
      int tmpm=get_arr(base,m-1);

      if(tmpi>pivot){
        if(tmpm<=pivot){
          upd_arr(base,i,tmpm);
          upd_arr(base,m-1,tmpi);
        }
        else{
          reverse_unfold(base,i,m-1);
          int tmp1 = partition(base,i,m-1,pivot);
          reverse_unfold_tail_2(base,tmp1,m);
          return tmp1;
        }
      }
      reverse_unfold_tail(base,i+1,m);
      int tmp2=partition(base,i+1,m,pivot);
      reverse_unfold_2(base,i,tmp2);
      return tmp2;
    }
    else{
      //i==m-1
      int tmpi=get_arr(base,i);
      if(tmpi>pivot){
        return i;
      }
      else{
        return m;
      }
    }
  }
}
