/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next; //#REC;	
}


HeapPred P(node x).
HeapPred P2(node x,node y).

/*

/* view for a singly linked list */
/*
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
*/
ll<> == self = null 
	or self::node<_, q> * q::ll<> 
  inv true;


lseg<p> == self = p
  or self::node<_, q> * q::lseg<p> //& self != p
  inv true;

lemma_safe "cir" self::clist<> 
   <- self::lseg<q2>*q2::node<_,self>.
   
lemma_unsafe "lseg" self::lseg<p> <- self::lseg<q>*q::node<_,p>;

/*
lemma_unsafe "lseg" self::node<_,q1>*q1::lseg<p> 
    <-> self::lseg<q>*q::node<_,p>;
*/

clist<> == selfe ::node<_,q>*q::lseg<self>;

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

clist2<> == 
  self::node<_,q>*q::lseg<self>
  or self::lseg<q2>*q2::node<_,self>;
  
clist3<> == self::node<_, q> * P2(q, self);

//clist2<> --> self::node<_,q>*q::lseg<self>;
//clist2<> <-- self::lseg<q2>*q2::node<_,self>;

//lemma_safe "cir" self::clist<> -> self::clist2<>.

*/

int len_seg(node x)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
/* infer [P,@classic]
  requires P(x)
  ensures false;
*/
  //requires x::clist<>  ensures false;
  //requires x::clist2<>  ensures false;
  infer [P,@classic]//@pure_field]
  requires P(x) //x::node<_, q> * P2(q, x)
  ensures false;
{    
  if (x==null) return 0;
  else { 
    node n = x.next;
    //dprint;
    int r=len_seg(n);
    // dprint;
    return 1+r;
  }
}

/*
# ex20e9a.ss -dre "infer_collect_hp_rel"

[ // BIND
(2;0)P2(x,p)&
x!=null --> x::node<val_74_1706,next_74_1707>@M * 
            HP_1708(next_74_1707,p,x@NI)&
true,
 // PRE_REC
(2;0)HP_1708(n',p,x@NI) * x::node<val_74_1706,n'>@M&
true --> P2(n',p_1711) * HP_1714(p)&
true,
 // POST
P2(x,p)&true --> htrue&
x!=null]


# Why HP_33/HP_1714 lost in hip inference

 <1>emp&n'=next_74_1707 & x'=x & x'!=null & !(v_bool_72_1621')&{FLOW,(20,21)=__norm#E}[]
 inferred hprel: [HP_33(p)&true --> emp&true; 
                  HP(n',p,x@NI) * x::node<val_74_1706,n'>@M&
                   true --> P2(n',p_1711) * HP_33(p)&true]


# why are we getting a complex RHS
      P2(n',p_1711) * HP_1714(p) ?

infer_collect_hp_rel#1@8 EXIT:(true,2:  HP_1714(p)&!(v_bool_72_1621') & x'!=null & x'=x & n'=next_74_1707&
{FLOW,(4,5)=__norm#E}[]
 es_infer_hp_rel: [(2;0)unknown HP_1708(n',p,x) * x::node<val_74_1706,n'>@M |#|  --> 
                    P2(n',p_1711) * HP_1714(p); 
                   (2;0)unknown P2(x,p)&
                    x!=null |#|  --> x::node<val_74_1706,next_74_1707>@M * 
                                     HP_1708(next_74_1707,p,x)]

--------------------------------------------

id: 24; caller: []; line: 76; classic: true; kind: PRE_REC; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ P2,HP_1708]; c_heap: emp; others:  es_infer_obj: [@leak] globals: [@dis_err,@leak]
 checkentail HP_1708(next_74_1707,p,x) * x::node<val_74_1706,next_74_1707>@M&
!(v_bool_72_1621') & x'!=null & x'=x & n'=next_74_1707 & MayLoop[]&
{FLOW,(4,5)=__norm#E}[]
 |-  P2(n',p_1711)&{FLOW,(4,5)=__norm#E}[]. 
hprel_ass: [ (2;0)unknown HP_1708(n',p,x) * x::node<val_74_1706,n'>@M |#|  --> P2(n',p_1711) * 
                                                                   HP_1714(p),
 (2;0)unknown P2(x,p)&
  x!=null |#|  --> x::node<val_74_1706,next_74_1707>@M * 
                   HP_1708(next_74_1707,p,x)]
ho_vars: nothing?
res:  1[
    HP_1714(p)&!(v_bool_72_1621') & x'!=null & x'=x & n'=next_74_1707&
{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]

*/
