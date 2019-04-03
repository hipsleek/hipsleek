data node2 {
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<p , q> * q::dll<self, n-1> & n > 0;
	// inv n >= 0;

void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0 & n > 0
	ensures x::dll<q, m+n>;

{
	if (x.next == null) {
		x.next = y.next;
    // x.next = y;
    y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}


// (==solver.ml#2636==)
// heap_entail_after_sat_struc#1@10
// heap_entail_after_sat_struc#1 inp1 :  q_1952::dll<self_1950,flted_8_1951>@M * y::dll<p,n>@M * 
//  x'::node2<p_1949,q_1952>@M&
// !(v_bool_16_1926') & 0<n & 0<m & y'=y & x'=x & self_1950=x' & p_1949=q & 
// flted_8_1951+1=m & q_1952!=null & v_node2_22_1925'=q_1952
//  es_gen_impl_vars(E): []
//  es_subst (from,to): []:[]
//  es_cond_path: [2; 0]
//  es_var_measures 1: Some(MayLoop[]{})
 

// heap_entail_after_sat_struc#1 inp2 : EBase 
//    exists (Impl)[q_1994; m_1995; p_1996; 
//    n_1997]v_node2_22_1925'::dll<q_1994,m_1995>@M * y'::dll<p_1996,n_1997>@M&
//    0<m_1995 & 0<n_1997
//    EBase 
//      emp&MayLoop[]
//      EAssume 
//        (exists q_104,
//        flted_13_103: v_node2_22_1925'::dll<q_104,flted_13_103>@M&
//        flted_13_103=n_1997+m_1995 & q_104=q_1994)
//        struct:EBase 
//                 (exists q_104,
//                 flted_13_103: v_node2_22_1925'::dll<q_104,flted_13_103>@M&
//                 flted_13_103=n_1997+m_1995 & q_104=q_1994)
// heap_entail_after_sat_struc#1@10 EXIT: [ (exists q_2002,
// flted_13_2003: x'::node2<p_1949,q_1952>@M * 
//                v_node2_22_1925'::dll<q_2002,flted_13_2003>@M&
// !(v_bool_16_1926') & 0<n & 0<m & y'=y & x'=x & self_1950=x' & p_1949=q & 
// flted_8_1951+1=m & q_1952!=null & v_node2_22_1925'=q_1952 & 
// q_1994=self_1950 & m_1995=flted_8_1951 & p_1996=p & n_1997=n & 0<=n & 
// 0<=flted_8_1951 & flted_13_2003=n_1997+m_1995 & q_2002=q_1994)
//   es_gen_impl_vars(E): []
//   es_pure: 0<n_1997 & 0<m_1995
//   es_subst (from,to): []:[]
//   es_cond_path: [2; 0]
//   es_var_measures 1: Some(MayLoop[]{})
  
//   es_unsat_flag: false]

