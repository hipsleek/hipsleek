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


lemma_unsafe self::arr_seg<i,n> & i<=m & m<=n 
   <-> self::arr_seg<i,m>*self::arr_seg<m,n>.

lemma_unsafe self::arr_seg_bounded<i,n,mi> & i<=m & m<=n 
  <-> self::arr_seg_bounded<i,m,mi>*self::arr_seg_bounded<m,n,mi>.

arr_seg_bounded<i,n,m> == i=n & i>=0
  or x::arrI<m0>*self::arr_seg_bounded<i+1,n,m> & x=self+i & i>=0 & m0<=m
  inv n>=i & i>=0;

/*
arr_seg_bounded<i,n,m> == i=n & i>=0
  or x::arrI<m0>*self::arr_seg_bounded<i,n-1,m> & x=self+(n-1) & i>=0 & m0<=m
  inv n>=i & i>=0;
*/

void bubble_push(arrI base, int start, int end)
 case {
  start=end -> ensures emp;
  start!=end ->
    requires base::arr_seg_bounded<start,end,m0>
    ensures  base::arr_seg_bounded<start,end-1,m1>*r::arrI<m> 
                 &r=base+(end-1) & m1<=m & m<=m0
    ;
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
    if(e1>e2){
      assume false;
      upd_arr(base,start,e2);
      upd_arr(base,start+1,e1);
      bubble_push(base,start+1, end);
    }
    else{
      //assume false;
      bubble_push(base,start+1,end);
    }
  }
}

/*

# fail due to insuff info ..

*/


