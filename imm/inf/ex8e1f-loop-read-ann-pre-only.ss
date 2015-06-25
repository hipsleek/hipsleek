data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [Q]
  requires c::cell<v>@a & Q(a)
  ensures c::cell<w>@b  ;

{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e1f.ss --trace-exc

# How come Q(a) = a=@L never printed?
  but in the end a=@L is added to pre-condition?

*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [Q]: ( Q(a)) -->  a<:@L,
RELDEFN Q: ( Q(a) & a<:@L & a<:a_1491) -->  Q(a_1491)]
*************************************

!!! **pi.ml#684:post_rel_ids:[]
!!! **pi.ml#685:reldefns:[( Q(a) & a<:@L & a<:a_1491, Q(a_1491)),( a<:@L, Q(a))]
!!! **pi.ml#686:reldefns_from_oblgs:[( a<:@L, Q(a))]
!!! **pi.ml#687:initial reloblgs:[( Q(a), a<:@L)]
!!! **pi.ml#688:reloblgs:[( Q(a), a<:@L)]
!!! **pi.ml#689:lst_assume:[( Q(a), a<:@L)]
!!! **pi.ml#690:pre_rel_fmls:[ Q(a)]
!!! **pi.ml#691:pre_ref_df:[( Q(a) & a<:@L & a<:a_1491, Q(a_1491)),( a<:@L, Q(a))]
!!! **pi.ml#692:WN: Need to form initial pre from reloblgs, namely P1(a) = a=@M
!!! **pi.ml#693:pre_ref_df:[( Q(a) & a<:@L & a<:a_1491, Q(a_1491)),( a<:@L, Q(a))]
!!! **pi.ml#694:post_ref_df:[]
!!! **pi.ml#695:post_vars:[c]
!!! **pi.ml#696:pre_vars:[v,Q,a,c]
!!! **pi.ml#711:post_ref_df_new:[]
!!! **pi.ml#721:pre_inv: Q(a)
!!! **pi.ml#722:post_inv: true
!!! **pi.ml#731:WN: need to process pre first
!!! **pi.ml#732:sp:compute_fixpoint:[]
!!! **pi.ml#733:
!!! **pi.ml#738:bottom_up_fp0:[]
!!! **pi.ml#749:pre_rel_fmls:[ Q(a)]
!!! **pi.ml#750:pre_fmls:[ Q(a) & c=2, MayLoop[]]
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **tpdispatcher.ml#1132:conversion of int to imm is disabled
!!! **fixcalc.ml#939:rel_defs:[( Q(a,pa), (a<=2 | (exists(a_1491:a<=a_1491 & Q(a_1491,pa)) & a<=2)),1)]
!!! **fixcalc.ml#940:No of disjs:1
!!! **fixcalc.ml#948:top down
!!! **fixcalc.ml#966:Input of fixcalc: :Q:={[a] -> [pa] -> []: (a<=2 ||  (exists (a_1491:a<=a_1491 && Q(a_1491,pa)))  && a<=2)
};
TD:=topdown(Q, 1, SimHeur);
TD;
!!! **fixcalc.ml#370:svls (orig):[Q,pa,a]
!!! **fixcalc.ml#371:svls (from parse_fix):[RECa,a]
!!! **fixcalc.ml#994:Result of fixcalc (parsed): :[ 2>=a & RECa>=a]
!!! fomega = gist {[Q,a] : (((0=0)))} given {[Q,a] : ((0=0))};

!!! fomega = gist {[Q,a] : (((0=0)))} given {[Q,a] : ((0=0))};

!!! **pi.ml#755:fixpoint:[( true, true, Q(a), true)]
!!! **pi.ml#760:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#761:>>REL POST:  true
!!! **pi.ml#762:>>POST:  true
!!! **pi.ml#763:>>REL PRE :  Q(a)
!!! **pi.ml#764:>>PRE :  true
!!! **pi.ml#783:>>>>>>>>>>> (after postprocess): <<<<<<<<<
!!! **pi.ml#784:>>REL POST :  true
!!! **pi.ml#785:>>POST:  true
!!! **pi.ml#786:>>REL PRE :  Q(a)
!!! **pi.ml#787:>>PRE :  true
!!! **pi.ml#813:new_specs1:[ EInfer [Q]
   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&Q(a)&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists b_1459,w_1460: c::cell<w_1460>@b_1459&
                     {FLOW,(4,5)=__norm#E}[]
                     ]
!!! **pi.ml#820:new_specs2:[ EInfer [Q]
   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@L&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists b_1459,w_1460: c::cell<w_1460>@b_1459&
                     {FLOW,(4,5)=__norm#E}[]
                     ]
Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@L & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists b_1459,w_1460: c::cell<w_1460>@b_1459&
           {FLOW,(4,5)=__norm#E}[]



*/
