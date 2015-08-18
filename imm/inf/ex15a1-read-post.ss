
data cell{
 int fst;
}

relation Q(ann v).

int foo2(cell c, cell d)
infer [@imm_pre]
  requires c::cell<yyy> * d::cell<yyy>@A
  ensures c::cell<yyy>@b * d::cell<yyy>;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

/*
relation P(ann v1).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
  infer [@imm_post]
  requires c::cell<v>@M
  ensures c::cell<w>@b ;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}


relation P(ann v1, ann v2).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
  infer [@imm_pre]
  requires c::cell<v>@a*y::cell<>*x::cell<>@L & P(a,b)
  ensures c::cell<w>;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}
 
P(a,b) a=@M & b=@A


//// why  yyy:int=@A?? 

remove_abs_nodes_struc@1
remove_abs_nodes_struc inp1 : EBase 
   exists (Expl)[](Impl)[ann_1439:AnnT; 
   yyy:int](ex)[]c:cell::cell<yyy:int>@ann_1439:AnnT * 
                 d:cell::cell<yyy_38:int>@A&
   yyy_38:int=yyy:int & ann_1439:AnnT=@M & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists yyy_39:int,yyy_40:int,ann_1438:AnnT,
     b:AnnT: c:cell::cell<yyy_39:int>@b:AnnT * 
             d:cell::cell<yyy_40:int>@ann_1438:AnnT&
     {FLOW,(4,5)=__norm#E}[]
remove_abs_nodes_struc@1 EXIT: EBase 
   exists (Expl)[](Impl)[ann_1439:AnnT; 
   yyy:int](ex)[]c:cell::cell<yyy:int>@ann_1439:AnnT&
   yyy:int=@A & ann_1439:AnnT=@M & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists yyy_39:int,yyy_40:int,ann_1438:AnnT,
     b:AnnT: c:cell::cell<yyy_39:int>@b:AnnT * 
             d:cell::cell<yyy_40:int>@ann_1438:AnnT&
     {FLOW,(4,5)=__norm#E}[]

*/
