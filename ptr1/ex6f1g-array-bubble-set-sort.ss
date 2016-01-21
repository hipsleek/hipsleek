data arrI {
  int val;
}

arr_seg<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_seg<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2)
  inv n>=i & i>=0;

arr_sorted<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_sorted<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2) 
     & forall(a:a notin S2 | v<=a)
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

/*
lemma_unsafe self::arr_seg<i,n,S> & i<=m & m<n 
  <-> self::arr_seg<i,m,S1>*self::arr_seg<m,n,S2> & S=union(S1,S2).
*/

/*
lemma_unsafe self::arr_seg<i,n,S> & i<n <-> 
  self::arr_seg<i,n-1,S1>*r::arrI<m> & r=self+(n-1) & S=union(S1,{m}).
*/
  
lemma_unsafe self::arr_seg<i,n,S> & i<n & b=n-1 <-> 
  self::arr_seg<i,b,S1>*r::arrI<m> & r=self+(n-1) & S=union(S1,{m}).
  
lemma_unsafe self::arr_sorted<i,n,S> & i<n & b=n-1 <-> 
  self::arr_sorted<i,b,S1>*r::arrI<m> & r=self+(n-1) & S=union(S1,{m})
  & forall(a: a notin S1 |  a<=m).

lemma_unsafe self::arr_seg<i,n,S> & (i>=n-1) -> self::arr_sorted<i,n,S>.
  // does folding use i>=n-1 on RHS too?

lemma_unsafe self::arr_seg<i,n,S>
      <- self::arr_sorted<i,n,S>.

void bubble_push(arrI base, int start, int end)
 case {
  start=end -> ensures emp;
  start!=end ->
    requires base::arr_seg<start,end,S>
    ensures  base::arr_seg<start,end-1,S1>*r::arrI<m> 
  //&r=base+(end-1) & S=S1//S=union(S1,{m})
  & r=base+(end-1) & S=union(S1,{m}) & forall(a: a notin S1 |  a<=m)
    ;
 }
 //ensures base::arr_seg_min_head<start,end>;
{
  if(start>=end-1){
    // assume false;
    //dprint;
    return;
  }
  else{
    //assume false;
    int e1 = get_arr(base,start);
    int e2 = get_arr(base,start+1);
    if(e1>e2){
      //assume false;
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



void bubble_sort(arrI base, int start, int end)
  requires base::arr_seg<start,end,S> //& start<end
  ensures base::arr_sorted<start,end,S>;
{
  if(start>=end-1){
    //assume false;
    return;
  }
  else{
    //assume false;
    bubble_push(base,start,end);
    bubble_sort(base,start,end-1);
    return;
  }
}

/*
# ex6f1g.ss

arr_seg<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_seg<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2)
  inv n>=i & i>=0;

arr_sorted<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_sorted<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2) & forall(a:a notin S2 | v<=a)
  inv n>=i & i>=0;

# verified with 3 lemmas:

lemma_unsafe self::arr_seg<i,n,S> & i<n & b=n-1 <-> 
  self::arr_seg<i,b,S1>*r::arrI<m> & r=self+(n-1) & S=union(S1,{m}).

lemma_unsafe self::arr_sorted<i,n,S> & i<n & b=n-1 <-> 
  self::arr_sorted<i,b,S1>*r::arrI<m> & r=self+(n-1) & S=union(S1,{m})
  & forall(a: a notin S1 |  a<=m).

lemma_unsafe self::arr_seg<i,n,S> & (i>=n-1)
      <-> self::arr_sorted<i,n,S>.

# to check:

!!! **typechecker.ml#970:
 Before CheckPost : 4
!!! **typechecker.ml#973:
 After CheckPost : 3
[UNSOUNDNESS] WARNING : possible new unsatisfiable state from post-proving of ex6f1g-array-bubble-set-sort.ss_84:10_84:39

 */
