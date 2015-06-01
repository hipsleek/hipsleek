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

int foo(cell c)
  infer [Q]
  requires c::cell<v>@a & Q(a)
  ensures c::cell<w>@b  ;

!!! **fixcalc.ml#370:svls (orig):[Q,pa,a]
!!! **fixcalc.ml#371:svls (from parse_fix):[RECa,a]
!!! **fixcalc.ml#994:Result of fixcalc (parsed): :[ 2>=a & RECa>=a]
!!! fomega = gist {[Q,a] : (((0=0)))} given {[Q,a] : ((0=0))};


# @L exception failure.

!!! **pi.ml#743:pre_fmls:[ Q(a) & c=2, MayLoop[]]Exception(get_array_element_in_f):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
Exception(get_array_element_as_spec_var_list):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
Exception(compute_def):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")



*/
