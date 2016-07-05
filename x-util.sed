s/U\./Util./g
s/Util.\([hn]o\)_debug/Gen.Debug.\1/g
s/Util.add_to_counter/Gen.Profiling.add_to_counter/g
s/Util.inc_counter/Gen.Profiling.inc_counter/g
s/Util.push_time/Gen.Profiling.push_time/g
s/Util.pop_time/Gen.Profiling.pop_time/g
s/Util.prof_/Gen.Profiling.prof_/g
s/Util.print_profiling_info/Gen.Profiling.print_info/g
s/Util.\(string_of_counters\)/Gen.Profiling.\1/g
s/Util.\(gen_time_msg\)/Gen.Profiling.\1/g
s/Util.\(list_last\)/Gen.Profiling.\1/g
s/Util.\(add_index\)/Gen.Profiling.\1/g
s/Util.\(repeat\)/Gen.Profiling.\1/g

s/Util.restart/Gen.Basic.restart/g
s/Util.split_by/Gen.split_by/g
s/Util.\(split_at\)/Gen.\1/g
s/Util.\(empty\)/Gen.is_\1/g
s/Util.\(break_lines\)/Gen.\1/g
s/Util.\(unsome\)/Gen.\1/g
s/Util.\(is_some\)/Gen.\1/g
s/Util.\(replace_minus_with_uscore\)/Gen.\1/g
s/Util.\(replace_dot_with_uscore\)/Gen.\1/g
s/Util.\(replace_path_sep_with_uscore\)/Gen.\1/g
s/Util.\(trim_str\)/Gen.\1/g
s/Util.\(map4\)/Gen.\1/g
s/Util.\(new_line_str\)/Gen.\1/g
s/Util.\(combine3\)/Gen.\1/g
s/Util.\(find_one_dup\)/Gen.BList.find_one_dup_eq\1/g 
s/Util.\(list_equal\) /Gen.BList.\1_eq (=) /g
s/Util.\(list_find\)/Gen.BList.\1/g
s/Util.\(subset\) /Gen.BList.\1_eq (=) /g
s/Util.\(remove_elem\)/Gen.BList.\1_eq (=)/g
s/Util.\(remove_dups\)_f/Gen.BList.\1_eq/g
s/Util.\(remove_dups\)/Gen.BList.\1_eq (=)/g
s/Util.\(remove_dups_eq\)/Gen.BList.\1/g
s/Util.\(check_dups_eq\)/Gen.BList.\1/g
s/Util.\(intersect\) /Gen.BList.\1_eq (=) /g
s/Util.\(mem\) /Gen.BList.\1_eq (=) /g
s/Util.\(find_dups\)_f/Gen.BList.\1_eq/g
s/Util.\(find_dups\)/Gen.BList.\1_eq (=)/g
s/Util.\(take\)/Gen.BList.\1/g
s/Util.\(drop\)/Gen.BList.\1/g
s/Util.\(find_index\)/Gen.BList.\1/g
s/Util.intersect_fct/Gen.BList.intersect_eq/g
s/Util.difference_fct/Gen.BList.difference_eq/g
s/Util.difference_f/Gen.BList.difference_eq/g
s/Util.difference/Gen.BList.difference_eq (=)/g
s/Util.string_of_a_list/Gen.BList.string_of_f/g
s/Util.string_of_list/Gen.BList.string_of_f/g

s/Util.\(find_equiv_all\)_eq_raw/EMapSV.\1/g
s/Util.\(get_equiv\)_eq_raw/EMapSV.\1/g
s/Util.\(get_elems\)_eq_raw/EMapSV.\1/g
s/Util.\(add_equiv\)_eq_raw/EMapSV.\1/g
s/Util.\(add_equiv\)/EMapSV.\1/g
s/Util.\(is_equiv\)_eq/EMapSV.\1/g
s/Util.\(subs_eset\)_eq/EMapSV.\1/g
s/Util.\(find_equiv_elim\)_eq/EMapSV.\1/g
s/Util.\(is_empty\)_aset_eq/EMapSV.\1/g
s/Util.\(un_partition\)/EMapSV.\1/g
s/Util.\(partition\)_eq/EMapSV.\1/g

s/Util.empty_a_set_eq \<.*\>/EMapSV.mkEmpty/g

s/Util.empty_aset/EMapSV.mkEmpty/g
s/Util.build_aset_eq CP.eq_spec_var/EMapSV.build_eset/g
s/Util.merge_set_eq/EMapSV.merge_eset/g
s/Util.string_of_eq_set/EMapSV.string_of/g
s/Util.rename_eset_eq_with_pr_allow_clash/EMapSV.rename_eset_allow_clash/g
s/spec_var Util.eq_set/Gen.EqMap(CP.SV).emap/g

s/Util.is_disj eq/DisjSetSV.is_disj/g
s/Util.\(one_list_dset\)/DisjSetSV.\1/g
s/Util.\(singleton_dset\)/DisjSetSV.\1/g
s/Util.\(merge_disj_set\)/DisjSetSV.\1/g
s/Util.\(star_disj_set\)/DisjSetSV.\1/g
s/Util.\(conj_disj_set\)/DisjSetSV.\1/g
s/Util.\(or_disj_set\)/DisjSetSV.\1/g
s/Util.\(is_sat_dset\)/DisjSetSV.\1/g
s/Util.\(empty_dset\)/DisjSetSV.mkEmpty/g

s/CP.spec_var Util.d_set/Gen.DisjSet(CP.PtrSV).dlist/g
s/spec_var Util.d_set/Gen.DisjSet(CP.PtrSV).dlist/g


s/Util.\(empty_baga\)/BagaSV.mkEmpty/g
s/Util.\(is_sat_baga\)/BagaSV.\1/g
s/Util.\(or_baga\)/BagaSV.\1/g
s/Util.\(conj_baga\)/BagaSV.\1/g
s/Util.\(star_baga\)/BagaSV.\1/g

s/CP.spec_var Util.baga/Gen.Baga(CP.PtrSV).baga/g
s/P.spec_var Util.baga/Gen.Baga(P.PtrSV).baga/g
s/spec_var Util.baga/Gen.Baga(PtrSV).baga/g


s/Util.\(c_h\)/Gen.ExcNumbering.\1/g
s/Util.\(get_closest\)/Gen.ExcNumbering.\1/g
s/Util.\(has_cycles\)/Gen.ExcNumbering.\1/g
s/Util.\(clean_duplicates\)/Gen.ExcNumbering.\1/g
s/Util.\(add_edge\)/Gen.ExcNumbering.\1/g
s/Util.\(get_hash_of_exc\)/Gen.ExcNumbering.\1/g
s/Util.\(exc_sub_type\)/Gen.ExcNumbering.\1/g


s/Util.\(tag_list\)/Gen.Stackable.\1/g
 
s/Util.\(list_of_hash_values\)/Gen.HashUti.\1/g
s/Util.\(copy_keys\)/Gen.HashUti.\1/g
