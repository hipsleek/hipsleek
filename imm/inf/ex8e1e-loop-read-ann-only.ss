data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [Q]
  requires c::cell<v>@L
  ensures c::cell<w>@b & Q(b)  ;
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
# ex8e1e.ss --trace-exc

int foo(cell c)
  infer [Q]
  requires c::cell<v>@L
  ensures c::cell<w>@b & Q(b)  ;

# @L exception failure.

1:77:!!! **pi.ml#726: Q(b_1459) = ( @L<:b_1459) \/ ( Q(b_1500) & b_1500<=(b_1459-2))Exception(get_array_element_in_f):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
1:78:Exception(get_array_element_as_spec_var_list):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
1:79:Exception(compute_def):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
1:80:Exception(compute_fixpoint_aux):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")
1:81:Exception(compute_fixpoint):Failure("Trans_arr.extract_translate_scheme: @L To Be Implemented")


*/
