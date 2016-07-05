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
    
treep<> == self= null or  self::tree<_,c>* c::dll<self,parent> ;

dll<parent, prev> == self=null or self::node<c,n,prev,parent>*c::treep<>* n::dll<parent,self>;


bool check_tree (tree t)
requires t::treep<> ensures res;
{
   if (t.children==null) return true;
    else return check_child(t.children,t,t);
}

bool check_child (node l, tree par, node prv)
requires l::dll<par, prev> ensures res;
{
	if (l==null) return true;
	else if (l.parent==par && l.prev==prv) return check_child(l.next, par, l)&& check_tree(l.child);
	else return false;
}