data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b & P2(a,b)  ;
{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e1d.ss

# The false must be due to duplicated residue problem ..

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:hfalse&false&{FLOW,(4,5)=__norm#E}[]
       es_cond_path: [1; 0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: [P1; P2]
       es_infer_rel: [RELASS [P1]: ( P1(a)) -->  a<:@L; 
                      RELASS [P1]: ( P1(a)) -->  a<:@L; 
                      RELDEFN P1: ( P1(a) & a<:@L & a<:a_1491) -->  P1(a_1491)]
 Exc:None
 ]

 |-  c'::cell<v_1492>@a_1491&P1(a_1491)&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN P1: ( P1(a) & a<:@L & a<:a_1491) -->  P1(a_1491)]
ho_vars: nothing?
res:  1[
   c::cell<v>@[@a, @a_1491]&v_bool_15_1452' & x'!=1 & P1(a) & c'=c & a<:@L & 
     x'=v & v_int_17_1450'=2 & a<:a_1491 & v_1492=v&{FLOW,(4,5)=__norm#E}[]
   ]


   c::cell<v>@[@a, @a_1491]&v_bool_15_1452' & x'!=1 & P1(a) & c'=c & a<:@L & 
     x'=v & v_int_17_1450'=2 & a<:a_1491 & v_1492=v&{FLOW,(4,5)=__norm#E}
     * c::cell<w>@b & P2(a,b)

 c::cell<v>@[a-b]*c::cell<w>@d
 ==> 

*/
