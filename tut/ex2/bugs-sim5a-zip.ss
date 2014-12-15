
relation P(int n,int m).
relation Q(int n,int m,int r).

void is_zero(int m)
  requires m=0
  ensures true;

void is_pos(int m)
  requires m>0 ensures true;


int zip(int n,int m)
  infer [P]
  requires P(n,m) ensures true;
{
  if (n==0) {
    //      is_zero(m);
      return 0;
  }
  else {
       is_pos(m);
       is_pos(n);
       return 1;
  }
}


/*
# bugs-sim5a-zip.ss

How come no relational assumption printed?

id: 2; caller: []; line: 18; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ P]; c_heap: emp
 checkentail emp&n'=0 & P(n,m) & m'=m & n'=n & v_bool_17_1315' & n'=n' & v_bool_17_1315'&
{FLOW,(4,5)=__norm#E}[]
 |-  emp&m'=0&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELASS [P]: ( P(n,m)) -->  m=0]
res:  1[


*/
