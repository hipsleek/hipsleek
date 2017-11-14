hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* S - server, C - client
   ms -  server's mailbox
   mc -  client's mailbox
*/
pred_sess_prot H<S:role,C:role,ms:chan,mc:chan> == C->S:ms(1) ;; S->C:mc(v#v>0);



/*
../../../../hip ex2a2-simplify-ctx-neq-bags.ss --sess -dre "simplify_context"

To check how to avoid the below disjunction:


(====)
simplify_context@6743@6742
simplify_context inp1 :  mc::OPENED<P,G,c1'>@M * ms::OPENED<P,G,c2'>@M&
bb_2463=mc & self_2472=G & flted_58_150={aa_2462,bb_2463} & 
aa_2462!=bb_2463 & Univ(aa_2462) & Univ(bb_2463) & x'=x & flted_58_150={ms,
mc} & P={C,S} & ms!=mc & C!=S&{FLOW,(4,5)=__norm#E}
 es_gen_impl_vars(E): []
 es_pure: G=G & self_2472=G
 es_subst (from,to): []:[]
 es_cond_path: [0]
 es_var_measures 1: Some(MayLoop[]{})
 
simplify_context@6743 EXIT:  mc::OPENED<P,G,c1'>@M * ms::OPENED<P,G,c2'>@M&
x=x' & S!=C & 
(((ms<mc & mc!=aa_2499) | (mc<=(aa_2499-1) & mc<=(ms-1)) | 
  (aa_2499<mc & mc<ms))) & 
P={C,S} & Univ(aa_2499) & Univ(mc) & {aa_2499,mc}={ms,mc}&
{FLOW,(4,5)=__norm#E}
 es_gen_impl_vars(E): []
 es_pure: G=G & self_2472=G
 es_subst (from,to): []:[]
 es_cond_path: [0]
 es_var_measures 1: Some(MayLoop[]{})
*/


void main(node x )
   requires [G,C,S,P,ms,mc] G::INITALL<{ms,mc}> & P={C,S} & ms!=mc & C!=S
   ensures  true; 
{
  dprint;
  Channel c1 = open () with (mc,P,G);
  dprint;
  Channel c2 = open () with (ms,P,G);
  dprint;
}

