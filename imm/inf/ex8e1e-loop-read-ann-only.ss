data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [Q]
  requires c::cell<v>@L
  ensures c::cell<w>@b & Q(b)  ;
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
need to define addition cause things go wrong without it ((b_1500:AnnT--2)<=b_1459:Ann):

from:
!!! **infer.ml#1979:lhs_p:: res:int=v_int_18_1504:int+2 & imm_1494:AnnT=@L+b_1500:AnnT & 
Q:RelT([])(b_1500:AnnT) & v_1488:int=v:int & c#':cell=c:cell & v:int!=1 & 
v_bool_16_1451#':boolean & imm_1494:AnnT<:b_1459:AnnT & w_1458:int=v:int

to:
!!! **infer.ml#1983:lhs_p_new (b4 filter ass):: v_int_18_1504:int+2=res:int & c:cell=c#':cell & w_1458:int=v_1488:int & 
v:int=v_1488:int & (b_1500:AnnT--2)<=b_1459:AnnT & c#':cell!=null & Q:RelT([])(b_1500:AnnT) & v_bool_16_1451#':boolean & (((imm_1494:AnnT=@I & 2<=v_1488:int) | (imm_1494:AnnT=@I & v_1488:int<=0)))


Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[v:int](ex)[]c:cell::cell<v:int>@L&MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists w_1458:int,
           b_1459:AnnT: c:cell::cell<w_1458:int>@b_1459:AnnT&
           b_1459:Unknown>=2&{FLOW,(4,5)=__norm#E}[]
           
why:  b_1459:Unknown>=2
=============================================================



# ex8e1e.ss --trace-exc

int foo(cell c)
  infer [Q]
  requires c::cell<v>@L
  ensures c::cell<w>@b & Q(b)  ;

# @L exception failure.

ERROR: at _0:0_0:0
Message: compute_def:Error in translating the input for fixcalc
Exception(compute_def):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint_aux):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint):Failure("compute_def:Error in translating the input for fixcalc")



*/
