relation P(int n).

void posint(int n)
  requires n>0  ensures true;

void foo(int n)
  infer [P]
  requires P(n)
  ensures true;
{
  posint(n); // assert n>0 assume n>0;
}



/*
# sim1-pre.ss --esl

GOT:
  
!!! proc_specs:[ EInfer [P]
   EBase emp&P(n)&{FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     htrue&{FLOW,(4,5)=__norm#E}[]
                     ]Stop Omega... 71 invocations 

(i) Can we print relational assumption
     P(n) --> n>=1
(ii) Why did we not replace P(n) = n>=1


id: 0; caller: []; line: 13; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ P]; c_heap: emp
 checkentail emp&P(n) & n'=n&{FLOW,(4,5)=__norm#E}[]
 |-  emp&0<n'&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELASS [P]: ( P(n)) -->  1<=n]
res:  1[
   emp&P(n) & n'=n & 1<=n&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [P]
   es_infer_rel: [RELASS [P]: ( P(n)) -->  1<=n]
   ]

*/
