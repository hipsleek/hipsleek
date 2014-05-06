data tree {
    int val; 
    node children;
    }
    
data node {
    tree child; 
    node next; 
    tree parent;
    }

PostPred G1(tree a).
PostPred G3(tree a).
PostPred G2(node a,tree b,node c).

treep<> == 
  self::tree<_,c>* c::sll<self> ;

sll<parent> == 
  self=null or 
  self::node<c,n,parent>*c::treep<>* n::sll<parent>;

bool check_tree (tree t)
  requires t::treep<>@L //& t!=null 
  ensures res;
{
   if (t.children==null) return true;
   else return check_child(t.children,t); 
}

bool check_child (node l, tree par)
  requires l::sll<par>@L 
  ensures  res;
{
	if (l==null) return true;
	else if (l.parent==par) return check_child(l.next, par)&& check_tree(l.child);
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
