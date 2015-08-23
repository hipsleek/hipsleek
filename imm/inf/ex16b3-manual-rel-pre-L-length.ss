
data node{
 int val;
 node next;
}

ll<n> == self=null & n=0 or
  self::node<_,q>*q::ll<n-1>
  inv n>=0;

relation P(ann a).

int length(node x)
  infer [P]
  requires x::ll<n>@b & P(b)
  ensures  x::ll<n>@a;
{
  if (x == null) return 0;
  else{
    dprint;
    //x::ll<n>@b&x'=x & x!=null & P(b)&
    int tmp = length(x.next);
    dprint;
    return tmp + 1;
  }
}


/**

FIXED by removing quatif and add it back after simplif
prune_eq_top_bot_imm_disjunct@2812@2811@2629
prune_eq_top_bot_imm_disjunct inp1 : exists(a_1495:exists(imm_1486:exists(b_1475:exists(imm_1485:@L<:imm_1485 & 
                                                             imm_1485=b_1475) & 
                                             b<:b_1475 & 
                                             (((b=imm_1486 & imm_1486<:b_1475) | 
                                               (b=b_1475 & 
                                                b_1475<:imm_1486 & 
                                                b_1475!=imm_1486)))) & 
                               exists(imm_1487:((imm_1487=imm_1486 & 
                                                 imm_1486<:a_1495) | 
                                                (imm_1487=a_1495 & 
                                                 a_1495<:imm_1486 & 
                                                 a_1495!=imm_1486))) & 
                               (((@A=a_1495 & a_1495<:imm_1486) | 
                                 (@A=imm_1486 & imm_1486<:a_1495 & 
                                  imm_1486!=a_1495))))) & 
 b<:@L
prune_eq_top_bot_imm_disjunct@2812 EXIT:true

(====)
is this really safe to prune?

prune_eq_top_bot_imm@2811@2629
prune_eq_top_bot_imm inp1 : exists(a_1495:exists(imm_1486:exists(b_1475:exists(imm_1485:@L<:imm_1485 & 
                                                             imm_1485=b_1475) & 
                                             b<:b_1475 & 
                                             (((b=imm_1486 & imm_1486<:b_1475) | 
                                               (b=b_1475 & 
                                                b_1475<:imm_1486 & 
                                                b_1475!=imm_1486)))) & 
                               exists(imm_1487:((imm_1487=imm_1486 & 
                                                 imm_1486<:a_1495) | 
                                                (imm_1487=a_1495 & 
                                                 a_1495<:imm_1486 & 
                                                 a_1495!=imm_1486))) & 
                               (((@A=a_1495 & a_1495<:imm_1486) | 
                                 (@A=imm_1486 & imm_1486<:a_1495 & 
                                  imm_1486!=a_1495))))) & 
 b<:@L
prune_eq_top_bot_imm@2811 EXIT: true


=============================================

simplify below:
@A=max(imm_1486,a_1495) & b=min(imm_1486,b_1475) & imm_1485=max(b,b_1475) & 
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) & flted_8_1468=n_1476 & 
 b<:b_1475 & b<:@L & x'=x & P(b) & x'!=null & !(v_bool_18_1446') & 
 flted_8_1468+1=n & v_int_24_1445'=1+tmp_1497 & res=v_int_24_1445' & 
 (((1<=flted_8_1468 & q_1470!=null) | (q_1470=null & flted_8_1468=0))) & x'=2


@A=max(imm_1486,a_1495) & b=min(imm_1486,b_1475) & imm_1485=b_1475 &  //because b<:b_1475
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) 
 b<:b_1475 & b<:@L


@A=imm_1486 & a_1495<:imm_1486 & b=min(imm_1486,b_1475) & imm_1485=b_1475 &  //because b<:b_1475
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) 
 b<:b_1475 & b<:@L
or
@A=a_1495 & imm_1486<:a_1495 & b=min(imm_1486,b_1475) & imm_1485=b_1475 &  //because b<:b_1475
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) 
 b<:b_1475 & b<:@L

=======================================================
from where do i get RELASS [P]: ( P(b)) -->  not(b<:@L)] ? (FIXED) - forgot to add the merge guards for view nodes

!!! **cvutil.ml#1217:elim_abs (pure):[]
*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [P]: ( P(b)) -->  b<:@A,
RELASS [P]: ( P(b)) -->  b<:@L,
RELDEFN P: ( P(b) & b<:@L & b<:b_1433) -->  P(b_1433),
RELASS [P]: ( P(b)) -->  not(b<:@L)]
*************************************

!!! **immutable.ml#62:imm + pure:[( not(b<:@L) & b<:@L & b<:@A, true)]
!!! **immutable.ml#64:imm + pure:[( false, true)]
***************************************
** relation obligations after imm norm **
*****************************************
[RELASS [P]: ( P(b)) -->  true]
*****************************************


 @A=max(imm_1486,a_1495) & b=min(imm_1486,b_1475) & imm_1485=max(b,b_1475) & 
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) & flted_8_1468=n_1476 & 
 b<:b_1475 & b<:@L & x'=x & P(b) & x'!=null & !(v_bool_18_1446') & 
 flted_8_1468+1=n & v_int_24_1445'=1+tmp_1497 & res=v_int_24_1445' & 
 (((1<=flted_8_1468 & q_1470!=null) | (q_1470=null & flted_8_1468=0))) & x'=2

(====)
HOW to solve simplif with ! not (FIXED) by calling the simplification at the merge call site rather than while callling the prover
>>>>>>>>> without emap
prune_eq_top_bot_imm@3682
prune_eq_top_bot_imm inp1 : (b<:a | 
  !(((((imm_1487=imm_1486 & imm_1486<:a_1495) | 
       (imm_1487=a_1495 & a_1495<:imm_1486 & a_1495!=imm_1486))) & 
     @L<:imm_1485 & 
     (((@A=a_1495 & a_1495<:imm_1486) | 
       (@A=imm_1486 & imm_1486<:a_1495 & imm_1486!=a_1495))) & 
     (((b=imm_1486 & imm_1486<:b_1475) | 
       (b=b_1475 & b_1475<:imm_1486 & b_1475!=imm_1486))) & 
     imm_1485=b_1475 & b<:b_1475 & b<:@L & P(b) & b<:a)))
prune_eq_top_bot_imm@3682 EXIT: b<:a


>>>>>>>>.with emap
prune_eq_top_bot_imm@3682
prune_eq_top_bot_imm inp1 : (b<:a | 
  !(((((imm_1487=imm_1486 & imm_1486<:a_1495) | 
       (imm_1487=a_1495 & a_1495<:imm_1486 & a_1495!=imm_1486))) & 
     @L<:imm_1485 & 
     (((@A=a_1495 & a_1495<:imm_1486) | 
       (@A=imm_1486 & imm_1486<:a_1495 & imm_1486!=a_1495))) & 
     (((b=imm_1486 & imm_1486<:b_1475) | 
       (b=b_1475 & b_1475<:imm_1486 & b_1475!=imm_1486))) & 
     imm_1485=b_1475 & b<:b_1475 & b<:@L & P(b) & b<:a)))
prune_eq_top_bot_imm@3682 EXIT: (b<:a | 
  !(((((imm_1487=imm_1486 & imm_1486<:a_1495) | 
       (imm_1487=a_1495 & a_1495<:imm_1486 & a_1495!=imm_1486))) & 
     @L<:imm_1485 & 
     (((@A=a_1495 & a_1495<:imm_1486) | 
       (@A=imm_1486 & imm_1486<:a_1495 & imm_1486!=a_1495))) & 
     (((b=imm_1486 & imm_1486<:b_1475) | 
       (b=b_1475 & b_1475<:imm_1486 & b_1475!=imm_1486))) & 
     imm_1485=b_1475 & b<:b_1475 & b<:@L & P(b) & b<:a)))


#ex16b3 detecting contra (it shouldn't) why b!=@L??

@3520! **solver.ml#5395:infer_vars_rel:[P]
@3520! **solver.ml#5396:infer_vars_sel_hp_rel:[]
@3520! **solver.ml#5397:infer_vars_sel_post_hp_rel:[]
@3520! **solver.ml#5398:orig_inf_vars:[]
@3520! **solver.ml#5498:WARNING: early_hp_contra_detection : :..in None
XXXX push_list(es_infer_rel:1)[RELASS [P]: ( P(b)) -->  b!=@L]

(==solver.ml#5502==)
add_infer_rel_to_estate@3722@3520
add_infer_rel_to_estate inp1 :[RELASS [P]: ( P(b)) -->  b!=@L]
add_infer_rel_to_estate@3722 EXIT:[RELASS [P]: ( P(b)) -->  b!=@L,RELDEFN P: ( P(b) & b<:@L & b<:b_1475) -->  P(b_1475),RELASS [P]: ( P(b)) -->  b<:@L]

==========================================================================
# ex16b3.ss
why contra detected? why adding !(b<:@L)  as a rel assume? where did !(b<:@L) disappear?

@1675!ex16b3-manual-rel-pre-L-length.ss:16: 11: [entail:16][post:16]**infer.ml#720:ovrlap inf vars: :[b]
@1675!ex16b3-manual-rel-pre-L-length.ss:16: 11: [entail:16][post:16]**infer.ml#721:pre infer   : : !(b<:@L)
@1675!ex16b3-manual-rel-pre-L-length.ss:16: 11: [entail:16][post:16]**infer.ml#722:new pre infer   : : !(b<:@L)
@1675!ex16b3-manual-rel-pre-L-length.ss:16: 11: [entail:16][post:16]**infer.ml#723:pre thus   : : true
@1675!ex16b3-manual-rel-pre-L-length.ss:16: 11: [entail:16][post:16]**infer.ml#784:rel_ass(unsat) : :Some( !(b<:@L))
@1675!ex16b3-manual-rel-pre-L-length.ss:16: 11: [entail:16][post:16]**infer.ml#805:rel_ass_final(unsat) : :[RELASS [P]: ( P(b)) -->  !(b<:@L)]
(==solver.ml#11719==)
infer_lhs_contra_estate#4@1675@1674@1673
infer_lhs_contra_estate#4 inp1 :estate: ex_formula : x'::node<Anon_1469,q_1470>@b&flted_8_1468+1=n & 
                                           !(v_bool_18_1446') & x'!=null & 
                                           x'=x & n_1476=flted_8_1468 & 
                                           n_1476=0 & q_1470=null & 
                                           flted_8_1468=0 & 
                                           v_int_24_1445'=1+tmp_1558 & 
                                           res=v_int_24_1445' & P(b) & 
                                           b<:@L & b<:b_1475&{FLOW,(4,5)=__norm#E}[]
 es_heap:emp
 es_infer_vars_rel: [P]
 es_infer_rel: [RELDEFN P: ( P(b) & b<:@L & b<:b_1475) -->  P(b_1475); 
                RELASS [P]: ( P(b)) -->  b<:@L]
 es_cond_path: [2; 0]
 es_var_measures 3: MayLoop
infer_lhs_contra_estate#4 inp2 :lhs_xpure:
 flted_8_1468+1=n & !(v_bool_18_1446') & x'!=null & x'=x & 
 n_1476=flted_8_1468 & n_1476=0 & q_1470=null & flted_8_1468=0 & 
 v_int_24_1445'=1+tmp_1558 & res=v_int_24_1445' & P(b) & b<:@L & b<:b_1475 & 
 x'!=null
infer_lhs_contra_estate#4 inp3 :EARLY CONTRA DETECTION
infer_lhs_contra_estate#4@1675 EXIT:(None,[( ex_formula : hfalse&false&{FLOW,(4,5)=__norm#E}[]
 es_heap:emp
 es_infer_vars_rel: [P]
 es_infer_rel: [RELDEFN P: ( P(b) & b<:@L & b<:b_1475) -->  P(b_1475); 
                RELASS [P]: ( P(b)) -->  b<:@L]
 es_var_measures 3: MayLoop,[RELASS [P]: ( P(b)) -->  !(b<:@L)],true)])

*/
