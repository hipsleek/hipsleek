data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [Q]
  requires c::cell<v>@a & Q(a)
  ensures c::cell<w>@b  ;

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
# ex8e1f.ss --trace-exc

*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [Q]: ( Q(a)) -->  a<:@L,
RELDEFN Q: ( Q(a) & a<:@L & a<:a_1491) -->  Q(a_1491)]
*************************************

int foo(cell c)
  infer [Q]
  requires c::cell<v>@a & Q(a)
  ensures c::cell<w>@b  ;


*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [Q]: ( Q(a)) -->  a<:@L,
RELDEFN Q: ( Q(a) & a<:@L & a<:a_1491) -->  Q(a_1491)]
*************************************

Q(a) = a=@L

 a=@L & a<:@L & a<:a1 -->  a1=@L


 I(a,a1) --> a<:a1
 a=@L & a<:@L & I(a,a1) -->  a1=@L

----------

!!! **fixcalc.ml#939:rel_defs:[( Q(a,pa), (a<=2 | (exists(a_1491:a<=a_1491 & Q(a_1491,pa)) & a<=2)),1)]
!!! **fixcalc.ml#940:No of disjs:1
!!! **fixcalc.ml#948:top down
!!! **fixcalc.ml#966:Input of fixcalc: :Q:={[a] -> [pa] -> []: (a<=2 ||  (exists (a_1491:a<=a_1491 && Q(a_1491,pa)))  && a<=2)
};
TD:=topdown(Q, 1, SimHeur);
TD;
!!! **fixcalc.ml#370:svls (orig):[Q,pa,a]
!!! **fixcalc.ml#371:svls (from parse_fix):[RECa,a]
!!! **fixcalc.ml#994:Result of fixcalc (parsed): :[ 2>=a & RECa>=a]
!!! fomega = gist {[Q,a] : (((0=0)))} given {[Q,a] : ((0=0))};

 State:c::cell<v>@imm_1504&exists(Q:Q(a)) & 
         exists(a_1491:exists(b_1511:exists(imm_1505:b_1511+
         imm_1505=imm_1504 & a=a_1491+imm_1505 & (imm_1505+a_1491)<:a_1491 & 
         (imm_1505+a_1491)<:@L))) & c=c' & x'=v & v!=1&
         {FLOW,(4,5)=__norm#E}[]

   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a<:@L&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists b_1459,w_1460: c::cell<w_1460>@b_1459&
                     {FLOW,(4,5)=__norm#E}[]
                     ]

!!! **fixcalc.ml#370:svls (orig):[Q,pa,a]
!!! **fixcalc.ml#371:svls (from parse_fix):[RECa,a]
!!! **fixcalc.ml#994:Result of fixcalc (parsed): :[ 2>=a & RECa>=a]
!!! fomega = gist {[Q,a] : (((0=0)))} given {[Q,a] : ((0=0))};


# @L exception failure.

!!! **pi.ml#743:pre_fmls:[ Q(a) & c=2, MayLoop[]]Exception(get_array_element_in_f):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
Exception(get_array_element_as_spec_var_list):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
Exception(compute_def):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")



*/
