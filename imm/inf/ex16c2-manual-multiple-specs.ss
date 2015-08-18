data cell {
 int fst;
 int snd;
}

sum<s> == self::cell<a,b> & s=a+b
  inv self!=null;

relation P1 (ann a).

void simple_read_write(cell c)
  infer [P1]
//  requires c::sum<n>@aaa & P1(aaa) //-------> this is fine
 requires c::sum<n>@a & P1(a)
  ensures c::sum<n+1>;
{
  dprint;
  int tmp = c.fst + 1;
  dprint;
  c.fst = tmp;
}


/**

Some renaming issue (FIXED):

Context of Verification Failure: ex16c2-manual-multiple-specs.ss_21:10_21:21

Last Proving Location: ex16c2-manual-multiple-specs.ss_24:12_24:17

Procedure simple_read_write$cell FAIL.(2)


Exception Failure("bind failure exception") Occurred!


Error(s) detected when checking procedure simple_read_write$cell

=====================================
a_1458 ann or int below? (FIXED)
//used as int
 c'=c & P1(a) & n=b_1459+a_1458 & fst_24_1436'=a_1458 & 
 snd_24_1437'=b_1459 & c'!=null

//used as ann
infer_pure_m_1 inp4 :rhs xpure : a_1458<:@L


(==infer.ml#1634==)
infer_pure_m_1@33@32@31@30@29@28@27@26@25@22@21@20@19@18@17@16@15@12@11@8@7@6@5@4@3@2@1
infer_pure_m_1 inp1 :estate :( pr_entail_state_short : Hole[1460]&c'=c & P1(a) & n=b_1459+a_1458 & 
                                    fst_24_1436'=a_1458 & snd_24_1437'=b_1459&{FLOW,(4,5)=__norm#E}[]
 es_heap:emp
 es_infer_vars_rel: [P1]
 es_cond_path: [0]
 es_var_measures 3: MayLoop,[])
infer_pure_m_1 inp2 :lhs xpure :
 P1(a) & c'=c & n=b_1459+a_1458 & fst_24_1436'=a_1458 & 
 snd_24_1437'=b_1459 & c'!=null
infer_pure_m_1 inp3 :lhs xpure0 :
 c'=c & P1(a) & n=b_1459+a_1458 & fst_24_1436'=a_1458 & 
 snd_24_1437'=b_1459 & c'!=null
infer_pure_m_1 inp4 :rhs xpure : a_1458<:@L
infer_pure_m_1 inp5 :inf vars :[]
infer_pure_m_1@33 EXIT:(new es,inf pure,rel_ass) :(None,None,[])



=================================
(FIXED)
(====)
subs_imm_par@64@61
subs_imm_par inp1 :[(a,a_1451),(b,b_1452)] <---- these refer to predicate's arguments
subs_imm_par inp2 :@a <---- this is ann
subs_imm_par@64 EXIT:@a_1451 <----- should be @a

(==cformula.ml#4465==)
subst@61
subst inp1 :[(a,a_1451),(b,b_1452)]
subst inp2 : (* lbl: *){219}->self::cell<a,b>@a&s=b+a&{FLOW,(1,28)=__flow#E}[]
subst@61 EXIT: (* lbl: *){219}->self::cell<a_1451,b_1452>@a_1451&s=b_1452+a_1451&
{FLOW,(1,28)=__flow#E}[]


*/
