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
 //c.fst = 5;
 return x;
}

/*
# ex8d1.ss

!!! **pi.ml#776:>>REL POST :  P2(a,v,b_1450,res,w_1451)
!!! **pi.ml#777:>>POST:  w_1451=res & v=res & a<:@L & a<:b_1450 & a<:@L
!!! **pi.ml#778:>>REL PRE :  P1(a,v)
!!! **pi.ml#779:>>PRE :  a<:@L

Post can simplify to:
!!! **pi.ml#777:>>POST:  w_1451=res & v=res & a<:@L & a<:b_1450 

Derived spec:
------------
requires c::cell<v>@a & a<:@L
ensures  c::cell<w>@b & w=res & v=res & a<:b 

Improving spec: 
---------------
(i) use weakest pre:
(ii) make strongest post:
requires c::cell<v>@a & a=@L
ensures  c::cell<w>@b & w=res & v=res & b=@L 
(iii) drop @L in post
requires c::cell<v>@a & a=@L
ensures  v=res  



Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a<:@L & a=@L & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists b_1450,w_1451: emp&res=v & w_1451=v & a=@L & b_1450=@A&
           {FLOW,(4,5)=__norm#E}[]
TODO:           
1. check why pre has the extra a<:@L
2. remove redundant info from post  w_1451=v & a=@L & b_1450=@A

*/
