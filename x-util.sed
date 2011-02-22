s/Util.\([hn]o\)_debug/Gen.Debug.\1/p
s/Util.add_to_counter/Gen.Profiling.add_to_counter/p
s/Util.inc_counter/Gen.Profiling.inc_counter/p
s/Util.push_time/Gen.Profiling.push_time/p
s/Util.pop_time/Gen.Profiling.pop_time/p
s/Util.prof_/Gen.Profiling.prof_/p
s/Util.print_profiling_info/Gen.Profiling.print_info/p
s/Util.\(string_of_counters\)/Gen.Profiling.\1/p
s/Util.\(gen_time_msg\)/Gen.Profiling.\1/p


s/Util.restart/Gen.Basic.restart/p
s/Util.split_by/Gen.split_by/p
s/Util.\(empty\)/Gen.\1/p
s/Util.\(break_lines\)/Gen.\1/p
s/Util.\(unsome\)/Gen.\1/p
s/Util.\(is_some\)/Gen.\1/p
s/Util.\(replace_minus_with_uscore\)/Gen.\1/p
s/Util.\(trim_str\)/Gen.\1/p
s/Util.\(map4\)/Gen.\1/p
s/Util.\(new_line_str\)/Gen.\1/p

s/Util.\(list_equal\) /Gen.BList.\1_eq = /p
s/Util.\(subset\) /Gen.BList.\1_eq = /p
s/Util.\(remove_elem\) /Gen.BList.\1_eq = /p
s/Util.\(remove_dups\) /Gen.BList.\1_eq = /p
s/Util.\(intersect\) /Gen.BList.\1_eq = /p
s/Util.\(mem\) /Gen.BList.\1_eq = /p
s/Util.\(remove_dups\)_f/Gen.BList.\1_eq = /p
s/Util.intersect_fct/Gen.BList.intersect_eq/p
s/Util.difference_fct/Gen.BList.difference_eq/p
s/Util.difference_f/Gen.BList.difference_eq/p
s/Util.string_of_a_list/Gen.BList.string_of_f/p
s/Util.string_of_list/Gen.BList.string_of_f/p

s/Util.\(find_equiv_all\)_eq_raw/Gen.EqMap(Slices.SV).\1/p
s/Util.\(add_equiv\)/Gen.EqMap(Slices.SV).\1/p
s/Util.\(is_equiv\)_eq/Gen.EqMap(Slices.SV).\1/p
s/Util.\(subs_eset\)_eq/Gen.EqMap(Slices.SV).\1/p
s/Util.\(find_equiv_elim\)_eq/Gen.EqMap(Slices.SV).\1/p
s/Util.\(is_empty\)_aset_eq/Gen.EqMap(Slices.SV).\1/p
s/Util.empty_aset/Gen.EqMap(Slices.SV).mkEmpty/p
s/Util.build_aset_eq CP.eq_spec_var/Gen.EqMap(Slices.SV).build_eset/p
s/Util.merge_set_eq/Gen.EqMap(Slices.SV).merge_eset/p
s/Util.string_of_eq_set/Gen.EqMap(Slices.SV).string_of/p
s/Util.rename_eset_eq_with_pr_allow_clash/Gen.EqMap(Slices.SV).rename_eset_allow_clash/p
s/Util.eq_set /Gen.EqMap(Slices.SV).emap/p

s/Util.is_disj eq/Gen.DisjSet(Slices.PtrSV).is_disj/p
s/Util.\(one_list_dset\)/Gen.DisjSet(Slices.PtrSV).\1/p
s/Util.\(singleton_dset\)/Gen.DisjSet(Slices.PtrSV).\1/p
s/Util.\(merge_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/p
s/Util.\(star_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/p
s/Util.\(conj_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/p
s/Util.\(or_disj_set\)/Gen.DisjSet(Slices.PtrSV).\1/p
s/Util.\(empty_dset\)/Gen.DisjSet(Slices.PtrSV).mkEmpty/p


s/Util.\(empty_baga\)/Gen.Baga(Slices.PtrSV).mkEmpty/p



s/Util.\(c_h\)/Gen.ExcNumbering.\1/p
s/Util.\(get_closest\)/Gen.ExcNumbering.\1/p

