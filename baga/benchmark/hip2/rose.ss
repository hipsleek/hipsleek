data tree {
    int val; 
    node children;
    }
    
data node {
    tree child; 
    node next; 
    tree parent;
    }

treep<n> == 
  self::tree<_,c>* c::sll<self,n-1> ;

sll<parent,s> == 
  self=null & s=0 or 
  self::node<c,n,parent>*c::treep<s1>* n::sll<parent,s2> & s=s1+s2+1;


bool check_tree (tree t)

requires t::treep<_> //& t!=null 
  ensures res;
{
   if (t.children==null) return true;
   else return check_child(t.children,t); 
}

bool check_child (node l, tree p)
  requires l::sll<p,_> 
  ensures  res;
{
	if (l==null) return true;
	else if (l.parent==p) return check_child(l.next, p)&& check_tree(l.child);
	else return false;
}
