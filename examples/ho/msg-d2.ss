data cell {
  int x;
}

data chan {
  int y;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

pred_prim MSG2<c:cell>
inv c!=null;

// "chan" type lost?
// what is the type for res in res::MSG{v::cell<1> & true}<v>?
chan create_msg (int x)
  requires true
  ensures (exists v: res::MSG{v::cell<1> & true}<v>);

/*
chan create_msg{%G}(int x)
  requires true ensures (exists v: res::MSG{%G}<v>);
*/

void send(chan ch, cell c)
    requires ch::MSG{%P}<c>@L * %P
    ensures  emp;

void receive(chan ch, ref cell c)
    requires ch::MSG{%PPP}<c>@L // do we use c or c'??
    ensures  %PPP & c'=c;

void main() 
 requires true
 ensures true;
{
  chan ch = create_msg(5);
  cell c = new cell(1);
  cell d;
  receive(ch,d);
  dprint;
}

/*
# msg-d2.ss

!!! Khanh : need to perform ho_var subs here
!!! residue(subs_ho): List of Failesc Context: [FEC(0, 0, 1  [])]

Successful States:
[
 Label: []
 State:(exists d_1244: ch_38'::MSG{ (exists flted_19_42: v_1241::cell<flted_19_4
2>&flted_19_42=1&
{FLOW,(24,25)=__norm})[]}<v_1241> * c_39'::cell<v_int_39_1242> * (HVar PPP)&v_in
t_39_1242=1 & d_40'=d_1244 & d_1244!=Cnull&{FLOW,(24,25)=__norm})[]
       es_heap: emp
       es_ho_vars_map: [PPP(exists flted_19_42: v_1241::cell<flted_19_42>&
                        d_40'=v_1241 & flted_19_42=1&
                        {FLOW,(24,25)=__norm})[]]
       es_var_measures 2: MayLoop[]
       es_cond_path: [0]

 ]

P should be substituted:

{FLOW,(24,25)=__norm})[]}<v_1241> * c_39'::cell<v_int_39_1242> * (HVar P)&v_int_39_1242=1 & d_40'!=Cnull&{FLOW,(24,25)=__norm}[]

# msg-d2.ss -dre "subst_h

subst_hvar@3
subst_hvar inp1 : (exists d_1244: ch_38'::MSG{ (exists flted_19_42: v_1241::cell<flted_19_42>&flted_19_42=1&
{FLOW,(24,25)=__norm})[]}<v_1241> * 
c_39'::cell<v_int_39_1242> * (HVar PPP)
& v_int_39_1242=1 & d_40'=d_1244 & d_1244!=Cnull&{FLOW,(24,25)=__norm})[]
subst_hvar inp2 :
     [(PPP, (exists flted_19_42: // #### where is exists v_1241 ??
  v_1241::cell<flted_19_42>&d_40'=v_1241 & flted_19_42=1&{FLOW,(24,25)=__norm})[])]
subst_hvar@3 EXIT: (exists flted_19_1245,
d_1244: ch_38'::MSG{ (exists flted_19_42: v_1241::cell<flted_19_42>&flted_19_42=1&
{FLOW,(24,25)=__norm})[]}<v_1241> * 
c_39'::cell<v_int_39_1242> 
* (HVar PPP)  //#### why is PPP still there after subst ??
* v_1241::cell<flted_19_1245> & flted_19_1245=1 & d_40'=v_1241  
& v_int_39_1242=1 & d_40'=d_1244 & d_1244!=Cnull 
&{FLOW,(24,25)=__norm})[]


*/
