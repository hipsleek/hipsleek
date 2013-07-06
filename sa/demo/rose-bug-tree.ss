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
  self::tree<_,c>* c::dll<self,null> ;

dll<parent, prev> == 
  self=null or 
  self::node<c,n,prev,parent>*c::treep<>* n::dll<parent,self>;


bool check_tree (tree t)
  requires t::treep<> 
  ensures res;
{
   if (t.children==null) return true;
   else //return check_child(t.children,t,null); 
        return check_child(t.children,t,t); //: (node * tree * tree)
}

bool check_child (node l, tree par, node prv)
  requires l::dll<par, prev> 
  ensures  res;
{
	if (l==null) return true;
	else if (l.parent==par && l.prev==prv) return check_child(l.next, par, l)&& check_tree(l.child);
	else return false;
}

/*
# rose-bug-tree.ss 

Typechecker has failed to pick this error!

Last Proving Location: 1 File "rose-bug-tree.ss",Line:26,Col:0

ERROR: at rose-bug-tree.ss_32:15_32:42 
Message: trans_exp :: case CallNRecv :: procedure 2 check_child$node~tree~tree is not found
 Stop Omega... 26 invocations Halting Reduce... 
caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("trans_exp :: case CallNRecv :: procedure 2 check_child$node~tree~tree is not found")


*/
