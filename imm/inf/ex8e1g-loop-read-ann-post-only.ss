data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [Q]
  requires c::cell<v>@a & a=@L //a=@L
  ensures c::cell<_>@b & Q(b); //c::cell<w>@b & b=@L  ;
/*
  requires c::cell<v>@a & a=@L
  ensures emp; //c::cell<w>@b & b=@L  ;
*/
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

# why no info abt b? given that:
*************************************
******pure relation assumption 1 *******
*************************************
[RELDEFN Q: ( Q(b_1507) & (b_1507+__CONST_Imm_@L)<:b_1463) -->  Q(b_1463),
RELDEFN Q: ( @L<:b_1463) -->  Q(b_1463)]
*************************************

# how come  __CONST_Imm_@L escaped the norm?

Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@L & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists Anon_1462,b_1463: c::cell<Anon_1462>@b_1463&
           {FLOW,(4,5)=__norm#E}[]  
-------------------------------------------------------------1

# ex8e1g.ss --trace-exc FIXED

Why did we get format error?

Exception(look_up_view_def_raw):Not_found
!!! **fixcalc.ml#160:fixcalc trans error :: (@L+b_1507)<:b_1463Exception(fixcalc_of_pure_formula(really called)):Globals.Illegal_Prover_Format("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")
Exception(fixcalc_of_pure_formula):Globals.Illegal_Prover_Format("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")
Exception(compute_def):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint_aux):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint):Failure("compute_def:Error in translating the input for fixcalc")
ExceptionFailure("compute_def:Error in translating the input for fixcalc")Occurred!
Exception occurred: Failure("compute_def:Error in translating the input for fixc



*/
