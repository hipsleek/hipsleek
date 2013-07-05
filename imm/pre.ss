void foo(int n)
 infer [n] requires true ensures n>5;
{
  n=n+2;
  test(n);
}

void test(int n)
 requires n>1 ensures true;

/*
# pre.ss

WHY only below:

!!! Inferred Pure :[ 0<=n]

However sleek-logging gives:
  es_infer_pure: [6<=n; 0<=n]
It seems that we did not take into account
the proving of post-condition.

 id: 4; caller: []; line: 4; classic: false; kind: POST; hec_num: 2; evars: []; c_heap: emp
 checkentail emp&n=n_758 & 0<=n&{FLOW,(22,23)=__norm}[]
 |-  emp&5<n&{FLOW,(22,23)=__norm}[]. 
res:  [
  emp&n=n_758 & 0<=n & 6<=n&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [n]
  es_infer_pure: [6<=n; 0<=n]
  ]


*/
