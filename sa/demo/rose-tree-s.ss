data tree {
    int val; 
    node children;
    }
    
data node {
    tree child; 
    node next; 
    node prev; 
    tree parent;
    }

PostPred G1(tree a).
PostPred G3(tree a).
PostPred G2(node a,tree b,node c).

treep<> == 
  self= null or
  self::tree<_,c>* c::dll<self,parent> ;

dll<parent, prev> == 
  self=null or 
  self::node<c,n,prev,parent>*c::treep<>* n::dll<parent,self>;


bool check_tree (tree t)
  requires t::treep<> & t!=null 
  ensures res;
{
  t.children=null;
  return true;
}


/*
# rose-tree.ss --pcp

Handled mutual recursive method but it seems
that there was an exception thrown..

WARNING: _0:0_0:0:View definitions [[treep,dll]] are mutually recursive
Stop Omega... 0 invocations caught

Exception occurred: Not_found
Error(s) detected at main 

*/
