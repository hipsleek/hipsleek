s/U\./Util./gp
s/Util.\([hn]o\)_debug/Gen.Debug.\1/gp
s/Util.add_to_counter/Gen.Profiling.add_to_counter/gp
s/Util.inc_counter/Gen.Profiling.inc_counter/gp
s/Util.push_time/Gen.Profiling.push_time/gp
s/Util.pop_time/Gen.Profiling.pop_time/gp
s/Util.prof_/Gen.Profiling.prof_/gp
s/Util.print_profiling_info/Gen.Profiling.print_info/gp
s/Util.\(string_of_counters\)/Gen.Profiling.\1/gp
s/Util.\(gen_time_msg\)/Gen.Profiling.\1/gp
s/Util.\(list_last\)/Gen.Profiling.\1/gp
s/Util.\(add_index\)/Gen.Profiling.\1/gp
s/Util.\(repeat\)/Gen.Profiling.\1/gp

s/Util.restart/Gen.Basic.restart/gp
s/Util.split_by/Gen.split_by/gp
s/Util.\(split_at\)/Gen.\1/gp
s/Util.\(empty\)/Gen.is_\1/gp
s/Util.\(break_lines\)/Gen.\1/gp
s/Util.\(unsome\)/Gen.\1/gp
s/Util.\(is_some\)/Gen.\1/gp
s/Util.\(replace_minus_with_uscore\)/Gen.\1/gp
s/Util.\(replace_dot_with_uscore\)/Gen.\1/gp
s/Util.\(replace_path_sep_with_uscore\)/Gen.\1/gp
s/Util.\(trim_str\)/Gen.\1/gp
s/Util.\(map4\)/Gen.\1/gp
s/Util.\(new_line_str\)/Gen.\1/gp
s/Util.\(combine3\)/Gen.\1/gp
s/Util.\(find_one_dup\)/Gen.BList.find_one_dup_eq\1/gp 
s/Util.\(list_equal\) /Gen.BList.\1_eq (=) /gp
s/Util.\(list_find\)/Gen.BList.\1/gp
s/Util.\(subset\) /Gen.BList.\1_eq (=) /gp
s/Util.\(remove_elem\)/Gen.BList.\1_eq (=)/gp
s/Util.\(remove_dups\)/Gen.BList.\1_eq (=)/gp
s/Util.\(remove_dups_eq\)/Gen.BList.\1/gp
s/Util.\(remove_dups\)_f/Gen.BList.\1_eq (=)/gp
s/Util.\(check_dups_eq\)/Gen.BList.\1/gp
s/Util.\(intersect\) /Gen.BList.\1_eq (=) /gp
s/Util.\(mem\) /Gen.BList.\1_eq (=) /gp
s/Util.\(find_dups\)_f/Gen.BList.\1_eq/gp
s/Util.\(take\)/Gen.BList.\1/gp
s/Util.\(drop\)/Gen.BList.\1/gp
s/Util.intersect_fct/Gen.BList.intersect_eq/gp
s/Util.difference_fct/Gen.BList.difference_eq/gp
s/Util.difference_f/Gen.BList.difference_eq/gp
s/Util.difference/Gen.BList.difference_eq (=)/gp
s/Util.string_of_a_list/Gen.BList.string_of_f/gp
s/Util.string_of_list/Gen.BList.string_of_f/gp

s/Util.\(find_equiv_all\)_eq_raw/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(get_equiv\)_eq_raw/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(get_elems\)_eq_raw/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(add_equiv\)/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(is_equiv\)_eq/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(subs_eset\)_eq/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(find_equiv_elim\)_eq/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(is_empty\)_aset_eq/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(un_partition\)/Gen.EqMap(Slices.SV).\1/gp
s/Util.\(partition\)_eq/Gen.EqMap(Slices.SV).\1/gp

s/Util.empty_a_set_eq \<.*\>/Gen.EqMap(Slices.SV).mkEmpty/gp

s/Util.empty_aset/Gen.EqMap(Slices.SV).mkEmpty/gp
s/Util.build_aset_eq CP.eq_spec_var/Gen.EqMap(Slices.SV).build_eset/gp
s/Util.merge_set_eq/Gen.EqMap(Slices.SV).merge_eset/gp
s/Util.string_of_eq_set/Gen.EqMap(Slices.SV).string_of/gp
s/Util.rename_eset_eq_with_pr_allow_clash/Gen.EqMap(Slices.SV).rename_eset_allow_clash/gp
s/spec_var Util.eq_set/Gen.EqMap(Slices.SV).emap/gp

s/Util.is_disj eq/Gen.DisjSet(Slices.PtrSV).is_disj/gp
s/Util.\(one_list_dset\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(singleton_dset\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(merge_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(star_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(conj_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(or_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(is_sat_dset\)/Gen.DisjSet(Slices.PtrSV).\1/gp
s/Util.\(empty_dset\)/Gen.DisjSet(Slices.PtrSV).mkEmpty/gp
s/CP.spec_var Util.d_set/Gen.DisjSet(Slices.PtrSV).dlist/gp
s/spec_var Util.d_set/Gen.DisjSet(Slices.PtrSV).dlist/gp


s/Util.\(empty_baga\)/Gen.Baga(Slices.PtrSV).mkEmpty/gp
s/Util.\(is_sat_baga\)/Gen.Baga(Slices.PtrSV).\1/gp
s/Util.\(or_baga\)/Gen.Baga(Slices.PtrSV).\1/gp
s/Util.\(conj_baga\)/Gen.Baga(Slices.PtrSV).\1/gp
s/Util.\(star_baga\)/Gen.Baga(Slices.PtrSV).\1/gp
s/CP.spec_var Util.baga/Gen.Baga(Slices.PtrSV).baga/gp
s/spec_var Util.baga/Gen.Baga(Slices.PtrSV).baga/gp
s/CP.spec_var Util.baga/Gen.Baga(Slices.PtrSV).baga/gp


s/Util.\(c_h\)/Gen.ExcNumbering.\1/gp
s/Util.\(get_closest\)/Gen.ExcNumbering.\1/gp
s/Util.\(has_cycles\)/Gen.ExcNumbering.\1/gp
s/Util.\(clean_duplicates\)/Gen.ExcNumbering.\1/gp
s/Util.\(add_edge\)/Gen.ExcNumbering.\1/gp
s/Util.\(get_hash_of_exc\)/Gen.ExcNumbering.\1/gp
s/Util.\(exc_sub_type\)/Gen.ExcNumbering.\1/gp


s/Util.\(tag_list\)/Gen.Stackable.\1/gp
 
s/Util.\(list_of_hash_values\)/Gen.HashUtil.\1/gp
s/Util.\(copy_keys\)/Gen.HashUtil.\1/gp
