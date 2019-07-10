data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

relation R(int n).

void id(node x, node y)
  infer [R]
  requires x::ll<nnn> & R(nnn)
  ensures true;
{
 x.next = null;
}

// infer [nnn] x::ll<nnn> |- x::node<a1,a2>
// 13732

/*

id: 8 src:5; caller: []; line: 15; classic: false; kind: BIND; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ nnn]; c_heap: emp; others:  es_infer_obj: [] globals: [@dis_err]
 checkentail hfalse&false&{FLOW,(4,5)=__norm#E}[]
 |-  x'::node<val_15_1875',next_15_1876'>@M&{FLOW,(1,28)=__flow#E}[].
ho_vars: nothing?
res:  1[
    hfalse&false&{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]

id: 9; caller: []; line: 15; classic: false; kind: BIND; hec_num: 1; evars: []; impl_vars: [val_15_1875',next_15_1876']; infer_vars: [ nnn]; c_heap: emp; others:  es_infer_obj: [] globals: [@dis_err]
 checkentail (exists flted_7_1889,Anon_1890,
q_1891: x'::node<Anon_1890,q_1891>@M * q_1891::ll<flted_7_1889>@M&
v_null_type_15_1874'=null & y'=y & x'=x & flted_7_1889+1=nnn & MayLoop[]&
{FLOW,(4,5)=__norm#E}[])
 |-  x'::node<val_15_1875',next_15_1876'>@M&{FLOW,(1,28)=__flow#E}[].
ho_vars: nothing?
res:  1[
    q_1895::ll<flted_7_1893>@M&
v_null_type_15_1874'=null & y'=y & x'=x & flted_7_1893+1=nnn &
val_15_1875'=Anon_1894 & next_15_1876'=q_1895&{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]
*/
