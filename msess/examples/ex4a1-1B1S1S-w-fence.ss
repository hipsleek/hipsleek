/* hip_include 'msses/notes/hodef.ss' */
/* hip_include 'msses/notes/commprimitives.ss' */

hip_include 'hodef.ss'
hip_include 'commprimitives.ss'


/*
data node {int info; node next;}
data adrr {int no;}
data date {int day; int year;}

pred_prim intt<a:int>;
pred_prim doublet<a:double>;

pred_prim D{%P}<>;
*/
/* buyer - seller - shipper */
/*
pred_sess_prot G<B,S,H> ==
  B->S: msg::intt<_>;;
  S->B: double;;
(  B->S: 1;;
   S->H: msg::intt<_>;;
   S->H: msg::D{@S B-> S: msg:: adrr< _>;; S-> B: msg:: date< _, _>}<>
   or B->S: 0);
*/


void buyer(Channel c, int id)
  requires  c::Chan{@S !0;;!1}<this>
  ensures   c::Chan{@S !1}<this>;
{
  dprint;
  send(c,0);
}


/**

either keep "this" as parameter for Chan
or avoid renaming of "this" in the specs

(==solver.ml#12944==)
do_match@1
do_match inp1 : c::Chan{ . this::Seq{ . this::S{ - emp&msg_101=0&{FLOW,(1,28)=__flow#E}}<msg_101>@M&
{FLOW,(1,28)=__flow#E}, . this::S{ - emp&msg_102=1&{FLOW,(1,28)=__flow#E}}<msg_102>@M&
{FLOW,(1,28)=__flow#E}}<>@M&
{FLOW,(1,28)=__flow#E}}<>@M
do_match inp2 : c'::Chan{ . this_1905::Seq{ . this_1905::S{ - HVar L[v_98]&{FLOW,(1,28)=__flow#E}}<v_98>@M&
{FLOW,(1,28)=__flow#E}, . HVar R[]&{FLOW,(1,28)=__flow#E}}<>@M&
{FLOW,(1,28)=__flow#E}}<>@M
do_match inp3 :  emp&v_int_35_1903'=0 & c'=c & id'=id&{FLOW,(4,5)=__norm#E}
 es_gen_impl_vars(E): [L; v_98; R; this_1905]
 es_subst (from,to): []:[]
 es_cond_path: [0]
 es_var_measures 1: Some(MayLoop[]{})
 es_trace:  SEARCH ==>  Match(c,c')
do_match inp4 : emp&{FLOW,(4,5)=__norm#E}
do_match inp5 :[]
do_match@1 EXIT: MustErr Context: 
   fe_kind: MUST
   fe_name: separation entailment
   fe_locs: {
     fc_message: matching of ho_args failed (do_unmatched_rhs : this_1905::Seq{ . this::S{ - HVar L[v_98]&{FLOW,(1,28)=__flow#E}}<v_98>@M&
{FLOW,(1,28)=__flow#E}, . HVar R[]&{FLOW,(1,28)=__flow#E}}<>@M(may))
     fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
   }
 [[ SEARCH ==>  Match(c,c')]]
 CEX:true
*/
