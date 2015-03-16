

data cell {
  int x;
}



int foo2(cell c)
  requires c::cell<n> & n>mmm
  ensures  res=n+1+mmm;

int foo(cell c)
  requires c::cell<n>
  ensures  c::cell<n+xxx>;

/*
wrap_post_struc_ex@1420@1415@1414@1413@1
wrap_post_struc_ex inp1 :[c,n,waitlevel,waitlevel',LSMU,LSMU',LS,LS',eres,res,n,mmm]
wrap_post_struc_ex inp2 :EBase: [][](EX  . (emp)*(res = (n+1)+mmm)( FLOW __norm)) 
wrap_post_struc_ex@1420 EXIT:EBase: [][](EX  . (emp)*(res = (n+1)+mmm)( FLOW __norm)) 

!!! struc_cont:Some(EAssume: 1,:(EX mmm . (emp)*(res = (n+1)+mmm)( FLOW __norm)))


case_normalize_renamed_formula@1242@1241@1240@1239@1
case_normalize_renamed_formula inp1 :view_decls:[memLoc]
case_normalize_renamed_formula inp2 :[c]
case_normalize_renamed_formula inp3 :[n,mmm]
case_normalize_renamed_formula inp4 :[]
case_normalize_renamed_formula inp5 :(emp ; (emp ; (c::cell{}<n>@M[HeapNode1])))*(n > mmm)( FLOW __norm)
case_normalize_renamed_formula@1242 EXIT:
 ### f = (EX  . (c::cell{}<n>@M[HeapNode1])*(n > mmm)( FLOW __norm))
 ### h = [n]
 ### expl = []

case_normalize_helper2@1241 EXIT:(
(None,[]): EBase: [ n][](EX  . (c::cell{}<n>@M[HeapNode1])*(n > mmm)( FLOW __norm)) {EAssume: 1,:(EX mmm . (emp)*(res = (n+1)+mmm)( FLOW __norm))},)

case_normalize_helper2@1231 EXIT:(
(None,[]): EBase: [ n][](EX  . (c::cell{}<n>@M[HeapNode1])*(true)( FLOW __norm)) {EAssume: 2,:(EX flted_15_38 xxx . (c::cell{}<flted_15_38>@M[HeapNode1])*(flted_15_38 = n+xxx)( FLOW __norm))},)

wrap_post_struc_ex@174
wrap_post_struc_ex inp1 :[c,n,waitlevel,waitlevel',LSMU,LSMU',LS,LS',eres,res,c,n]
wrap_post_struc_ex inp2 :EBase: [][](EX flted_15_37 . (c::cell{}<flted_15_37>@M[HeapNode1])*(flted_15_37 = n+xxx)( FLOW __norm)) 
wrap_post_struc_ex@174 EXIT:EBase: [][](EX flted_15_37 xxx . (c::cell{}<flted_15_37>@M[HeapNode1])*(flted_15_37 = n+xxx)( FLOW __norm)) 

wrap_post_struc_ex@175
wrap_post_struc_ex inp1 :[c,n,waitlevel,waitlevel',LSMU,LSMU',LS,LS',eres,res,n,mmm]
wrap_post_struc_ex inp2 :EBase: [][](EX  . (emp)*(res = (n+1)+mmm)( FLOW __norm)) 
wrap_post_struc_ex@175 EXIT:EBase: [][](EX  . (emp)*(res = (n+1)+mmm)( FLOW __norm)) 

Since m is in pre, we should not mark it as an exists in
the post.

int foo2$cell(  cell c)
static  :EBase exists (Expl)[](Impl)[n](ex)[]c::cell<n>&m<n&{FLOW,(24,25)=__norm}[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume 
                    (exists m: emp&res=m+n+1&{FLOW,(24,25)=__norm})[]
                    


*/
