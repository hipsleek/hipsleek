data cell{
 int fst;
}

relation P1(ann v1).
  relation P2(ann v1, ann v2,int v,int r).

int foo(cell c)
/*
  requires c::cell<v>@L
  ensures res=v;
*/
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
     ensures c::cell<v>@b & res=v & P2(a,b,v,res)  ;
//  requires c::cell<v>@L
//  ensures c::cell<v>@A & res=v  ;

/*
Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@L & a=@L & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1457,b_1458: c::cell<v_1457>@b_1458&v_1457=v & res=v & 
           b_1458=@A & a=@L&{FLOW,(4,5)=__norm#E}[]
*/
{
 int x = c.fst;
 return x;
}
/*
# ex3d7a.ss

  requires c::cell<v>@L
  ensures c::cell<v>@A & res=v  ;

# above succeeds but not below:

  requires c::cell<v>@a & a=@L
  ensures c::cell<v>@b & res=v & a=@A  ;

Post condition cannot be derived:
  (must) cause:  a<:ann_f_r_1493 & a=@L |-  a=@A. LOCS:[0;14;15] (must-bug)


*/
