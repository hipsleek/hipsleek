data arrI {
  int val;
}

arr_seg<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_seg<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2)
  inv n>=i & i>=0;

arr_sorted<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_sorted<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2) & forall(a:a notin S2 | v<=a)
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


void bubble_push(arrI base, int start, int end)
 case {
  start=end -> ensures emp;
  start!=end ->
    requires base::arr_seg<start,end,S>
    ensures  base::arr_seg<start,end-1,S1>*r::arrI<m> 
  //&r=base+(end-1) & S=S1//S=union(S1,{m})
  & r=base+(end-1) & S=union(S1,{m}) //& forall(a: a notin S1 |  a<=m)
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

/*

 */

/*

# success despite some complex formula (from unsat checks)

store dump :Imply: ante: 
n_2376=end_2249 & x_6448!=r_5822 & x_6276!=x_6448 & x_6276!=r_5822 & 
 x_2378!=x_6276 & x_2378!=x_6448 & x_2378!=r_5822 & r_5822!=null & 
 x_6448!=null & x_6276!=null & x_2378!=null & 1<=flted_6_2586 & 
 v_int_54_5825!=end' & v_int_54_5825=1+start' & n_2585=n_2376 & 
 start'<v_int_38_2339 & v_int_38_2339+1=end' & start'=start & end'=end & 
 start!=end & start_2248=start & end_2249=end & 0<=start_2248 & 
 flted_31_5821+1=end' & 0<=v_int_54_5825 & flted_6_6275=1+v_int_54_5825 & 
 x_6276=v_int_54_5825+base' & n_6274=flted_31_5821 & r_5822+1=end'+base' & 
 x_2587!=null & 0<=flted_6_2586 & flted_6_2586<=n_2585 & a=x_2378 & 
 flted_6_2377=1+start_2248 & x_2378=start_2248+base & base'=base & 
 0<=flted_6_2377 & x_2587=flted_6_2377+base & flted_6_2586=1+flted_6_2377 & 
 a_2495=x_2587 & flted_6_2586=(x_2587-base')+1 & base'<=x_2587 & 
 x_2587=(flted_6_2586+base')-1 & n_6446=n_6274 & 0<=flted_6_6275 & 
 x_6448=flted_6_6275+base' & flted_6_6447=1+flted_6_6275 & 
 (((0<=flted_6_6447 & ((0-base')+1)<=flted_6_6447 & flted_6_6447<n_6446 & 
    S2_6450=union({v_2017},S2_2018)) | 
   (n_6446=flted_6_6447 & 0<=flted_6_6447 & S2_6450={}))) & 
 S2_6278=union({v_6449},S2_6450) & S_3664=union({v_3746},S2_3747) & 
 S2_3747=S2_2589 & v_3746=v_2588 & v<=v_2496 & v_2496=v_2588 & 
 S2_2380=union({v_2588},S2_2589) & v=v_2379 & S1_5823=union({v_6277},
 S2_6278) & forall(a_6805:(a_6805 <notin> S_3664  | a_6805<=m_5824)) & 
 S_3664=union(S1_5823,{m_5824}) & S=union({v_2379},S2_2380)
	     conseq:  S=union({},{m_5824})

 // can we do auto-split for SAT formula?

 store dump :Sat:  flted_6_4780=1+v_int_50_4328 & x_4781=v_int_50_4328+base' & 
 0<=v_int_50_4328 & S1_4326=union({v_4782},S2_4783) & n_4779=flted_31_4324 & 
 forall(a:(a <notin> S1_4326  | a<=m_4327)) & S_3253=union(S1_4326,
 {m_4327}) & r_4325+1=end'+base' & flted_31_4324+1=end' & a_3067!=null & 
 0<=flted_6_2585 & flted_6_2585<=n_2584 & v_bool_46_1956' & v_3335=v & 
 v=v_2379 & a=x_2378 & flted_6_2377=1+start_2248 & x_2378=start_2248+base & 
 0<=start_2248 & S=union({v_2379},S2_2380) & n_2376=end_2249 & 
 !(v_bool_38_1957') & end_2249=end & start_2248=start & start!=end & 
 end'=end & start'=start & base'=base & v_int_38_2339+1=end' & 
 start'<v_int_38_2339 & n_2584=n_2376 & S2_2380=union({v_2587},S2_2588) & 
 0<=flted_6_2377 & x_2586=flted_6_2377+base & flted_6_2585=1+flted_6_2377 & 
 a_2495=x_2586 & v_2496=v_2587 & v_2496<v_3335 & a_2897=x_2378 & 
 Anon_11=v_2379 & x_2378!=null & a_3067=x_2586 & Anon_3068=v_2587 & 
 x_2586!=null & v_int_50_4328=1+start' & v_int_50_4328!=end' & 
 S2_3336=S2_2588 & flted_6_2585=(a_3067-base')+1 & base'<=a_3067 & 
 S_3253=union({v_3335},S2_3336) & a_3067=(flted_6_2585+base')-1 & 
 1<=flted_6_2585 & n_4955=n_4779 & S2_4783=union({v_4958},S2_4959) & 
 0<=flted_6_4780 & x_4957=flted_6_4780+base' & flted_6_4956=1+flted_6_4780 & 
 a_2897!=r_4325 & a_2897!=x_4957 & a_2897!=x_4781 & x_4781!=r_4325 & 
 x_4781!=x_4957 & x_4957!=r_4325 & a_2897!=null & x_4781!=null & 
 x_4957!=null & r_4325!=null & 0<=flted_6_4956 & 
 ((0-base')+1)<=flted_6_4956 & flted_6_4956<n_4955 & S2_4959=union({v_2017},
 S2_2018)


*/


void bubble_sort(arrI base, int start, int end)
  requires base::arr_seg<start,end,S> //& start<end
  ensures base::arr_seg<start,end,S>;
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
# ex6f1e.ss

bubble_push verifies but SAT takes much time; maybe
can split set-based from linear formula..

# -p bubble_sort
[mona] Warning: sat --> true(formula too large  - not sent to mona)


# -p bubble_push

# taking very long .. loop?

 */
