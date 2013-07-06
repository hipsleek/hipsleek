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
  //self=null or
  self::tree<_,c>* c::dll<self,null> ;

dll<parent, prev> == 
  self=null or 
  self::node<c,n,prev,parent>*c::treep<>* n::dll<parent,self>;


bool check_tree (tree t)
  requires t::treep<> //& t!=null 
  ensures res;
{
   node n = null;
   if (t.children==null) return true;
   else return check_child(t.children,t,n); 
    //check_child(t.children,t,t); // (node * tree * tree)
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
# rose-tree.ss --pcp

Handled mutual recursive method but it seems
that there was an exception thrown..

WARNING: _0:0_0:0:View definitions [[treep,dll]] are mutually recursive
Stop Omega... 0 invocations caught

Exception occurred: Not_found
Error(s) detected at main 

*/
