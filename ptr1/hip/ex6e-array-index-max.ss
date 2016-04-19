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
    requires base::arr_seg_max<i,m,maxv>
    ensures  base::arr_seg_max<i,m,res>;
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

//checkentail base::arr_seg<i_2028,m_2029>@M & !(v_bool_35_1976') & m_2029=m & i_2028=i & (i+1)<m & m'=m & i'=i & base'=base & v_int_35_2046+1=m' & i'!=v_int_35_2046 & v_int_40_1964'= 1+i' & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
//|-  (exists i_123,m_124: base'::arr_seg<i_123,m_124>@M&(v_int_40_1964'+1)<m' & i_123=v_int_40_1964' & m_124=m'& {FLOW,(4,5)=__norm#E}[]). 

/* // can base be monomorphic recursive? */
/* void init3(arrI base,int i,int m) */
/* /\*  requires base::arr_seg<i,m> * b2::arr_seg_map<i,m,M>@L//& 0<=i & i<=m */
/*   ensures  base::arr_seg_sorted<i,m,i>; */
/* *\/ */
/*  requires base::arr_seg<i,m> */
/*   case { */
/*    i>=m -> ensures emp; */
/*    i<m -> ensures base::arr_seg_sorted<i,m,i>; */
/*   } */
/* { */
/*   if (i<m) { */
/*     //assume false; */
/*     upd_arr(base,i,i); // base[i]=0 */
/*     i=i+1; */
/*     //a = arr_inc(a); */
/*     init3(base,i,m); */
/*   } */
/* } */

/*
# ex6e.ss 

# check and elim warnings below..


 !!! **astsimp.ml#2740:inconsistent roots:[[]]
!!! **astsimp.ml#2740:inconsistent roots:[[]]
!!! **astsimp.ml#2740:inconsistent roots:[[]]
!!! **astsimp.ml#2740:inconsistent roots:[[]]
!!! **astsimp.ml#2740:inconsistent roots:[[]]
!!! **astsimp.ml#2740:inconsistent roots:[[]]


*/
