data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_sorted<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0
  or x::arrI<mi>*self::arr_seg_sorted<i+1,n,m2> & x=self+i 
       & i>=0 & i<n-1 & mi<=m2
  inv n>i & i>=0;

arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2)
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

int get_max(arrI base,int i,int m)
/*
 requires base::arr_seg<i,m> 
 case{
  i>=m -> ensures emp & res=-1;
  i<m -> ensures base::arr_seg_max<i,m,res>;
  }
*/
 case{
  i>=m -> ensures emp & res=-1;
  i<m -> 
    requires base::arr_seg_max<i,m,mval>@L
    ensures  res=mval;
  }
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

/*
# ex6e1.slk

# Add source line number to messages below ..

!!! **WARNING****astsimp.ml#9214:Post-condition has existentially quantified free vars:[(q,)]
!!! **WARNING****astsimp.ml#9214:Post-condition has existentially quantified free vars:[(p,)]
!!! **WARNING****astsimp.ml#9214:Post-condition has existentially quantified free vars:[(mval,)]


 */
