data cell{
 int fst;
}

relation P1(ann v1, int v).
relation P2(ann v1, ann v2,int v,int r, int s).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a,v)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
 int x = c.fst;
 if (x>0) c.fst = 5;
 return x;
}

/*



========================================

# ex8d2.ss
 
to solve the hfalse due to norm_imm  a=@M & a<:@L ---> a=@M & a=@L

(====)
norm_rel_oblgs@4
norm_rel_oblgs inp1 :[( P1(a,v), (a=@M | (v<=0 & a<:@L) | a=@A)),( P1(a,v), a<:@L)]
norm_rel_oblgs@4 EXIT:[( P1(a,v), a=@M & a<:@L)]

(==tpdispatcher.ml#2210==)
norm_imm_rel_formula@5
norm_imm_rel_formula inp1 :[]
norm_imm_rel_formula inp2 : a=@M & a<:@L
norm_imm_rel_formula@5 EXIT: a=@M & a=@L

(====)
simplify_relation@7@6
simplify_relation inp1 : EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&P1(a,v)&
       {FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume 
                   (exists b_1456,w_1457: c::cell<w_1457>@b_1456&
                   P2(a,b_1456,v,res,w_1457)&{FLOW,(4,5)=__norm#E}[]
                   
simplify_relation inp2 :Some([( P2(a,v,b_1456,res,w_1457), ((a=@M & b_1456=@M & w_1457=res & v=res & res<=0) | (a=@M & b_1456=@M & 
w_1457=5 & v=res & 1<=res)), a=@M)])
simplify_relation inp3 :lst_assume:[( P1(a,v), a=@M & a=@L)]
simplify_relation@7 EXIT:( EBase exists (Expl)[](Impl)[a; v](ex)[]hfalse&false&{FLOW,(4,5)=__norm#E}[]
         EBase emp&a=@M & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume 
                   (exists b_1456,w_1457: c::cell<w_1457>@b_1456&((a=@M & 
                   b_1456=@M & w_1457=res & v=res & res<=0) | (a=@M & 
                   b_1456=@M & w_1457=5 & v=res & 1<=res))&
                   {FLOW,(4,5)=__norm#E}[]
                   ,[])
========================================================================

GOT
---
!!! **pi.ml#770:>>POST:  
((a=@M & res=w_1457 & v=w_1457 & w_1457<=0 & b_1456=@M) 
| (w_1457=5 & a=@M & v=res & b_1456=@M & 1<=res))

Can normalize to:
-----------------
!!! **pi.ml#770:>>POST:  
a=@M & b_1456=@M & ( res=w_1457 & v=w_1457 & w_1457<=0 ) 
                    | (w_1457=5 & v=res & 1<=res)


!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | (v<=0 & a<:@L)))]

Maybe can strengthen this to:

!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | a<:@L))]
!!! **pi.ml#696:reloblgs:[( P1(a,v), a=@M] [DONE]


if SAT(a=@M & (v<=0 & a<:@L)) then strengthen  (a=@M | (v<=0 & a<:@L))
strengthen  (a=@M | (v<=0 & a<:@L)) = 
 = strengthen (imm(a=@M | (v<=0 & a<:@L)) & strengthen (pure(a=@M | (v<=0 & a<:@L))
 = strengthen (a=@M | a<:@L) & strengthen (true | v<=0)
 = a=@M & true



*/
