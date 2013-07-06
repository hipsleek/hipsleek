data tree {
    int val; 
    node children;
    }
    
data node {
    tree child; 
    node prev; 
    node next; 
    tree parent;
    }

HeapPred H1(tree a).
PostPred G1(tree a).
HeapPred H2(node a,node@NI c,tree@NI b).
PostPred G2(node a,node@NI c,tree@NI b).

treep<> == 
  //self=null or
  self::tree<_,c>* c::dll<self,null> ;

dll<parent, prev> == 
  self=null or 
  self::node<c,prev,n,parent>*c::treep<>* n::dll<parent,self>;


bool check_tree (tree t)
  //requires t::treep<>@L ensures res;
  infer [H1,G1,H2,G2] requires H1(t) ensures G1(t) & res;
{
   node n = null;
   if (t.children==null) return true;
   else return check_child(t.children,n,t); 
    //check_child(t.children,t,t); // (node * tree * tree)
}

bool check_child (node l, node prv, tree par)
  //requires l::dll<par, prv>@L ensures  res;
  infer [H1,G1,H2,G2] requires G2(l,prv,par) ensures G2(l,prv,par) & res;
{
	if (l==null) return true;
	else if (l.parent==par && l.prev==prv) 
           return check_child(l.next,l, par)&& check_tree(l.child);
	else return false;
}

/*
# check-mcf.ss

[ G2(l,prv@NI,par@NI)&
  l!=null --> l::node<child_42_1006,prev_42_1007,next_42_1008,parent_42_1009>@M * 
  G_0(child_42_1006,prv@NI,par@NI) * 
  G_1(prev_42_1007,prv@NI,par@NI) * 
  G_2(next_42_1008,prv@NI,par@NI) * G_3(parent_42_1009,prv@NI,par@NI),
 G_2(next_42_1008,prv@NI,par@NI)&par=par' & 
  prev_42_1007=prv --> G2(next_42_1008,l@NI,par@NI),
 G_0(child_42_1006,prv@NI,par@NI)&par=par' & 
  prev_42_1007=prv --> H1(child_42_1006),
 G2(l,prv@NI,par@NI)&l=null --> G2(l,prv@NI,par@NI),
 G_1(prev_42_1007,prv@NI,par@NI) * 
  G_3(parent_42_1009,prv@NI,par@NI) * 
  l::node<child_42_1006,prev_42_1007,next_42_1008,parent_42_1009>@M * 
  G2(next_42_1008,l@NI,par@NI) * G1(child_42_1006)&par=parent_42_1009 & 
  prev_42_1007=prv --> G2(l,prv@NI,par@NI),
 G_1(prev_42_1007,prv@NI,par@NI) --> emp&
  forall(parent_42_1009:((par!=parent_42_1009 | prv>=prev_42_1007)) & 
  ((par!=parent_42_1009 | prev_42_1007>=prv))),
 G_1(prev_42_1007,prv@NI,par@NI) --> emp&
  forall(parent_42_1009:((prev_42_1007!=prv | par>=parent_42_1009)) & 
  ((prev_42_1007!=prv | parent_42_1009>=par))),
 G_1(prev_42_1007,prv@NI,par@NI) --> emp&
  forall(parent_42_1009:((par>=parent_42_1009 | prv>=prev_42_1007)) & 
  ((parent_42_1009>=par | prv>=prev_42_1007)) & ((par>=parent_42_1009 | 
  prev_42_1007>=prv)) & ((parent_42_1009>=par | prev_42_1007>=prv)))]


[ H1(t) --> t::tree<val_32_1082,children_32_1083>@M * 
  HP_1084(children_32_1083),
 HP_1084(children_32_1083)&
  children_32_1083!=null --> G2(children_32_1083,n_38'@NI,t@NI),
 HP_1084(children_32_1083) * t::tree<val_32_1082,children_32_1083>@M&
  children_32_1083=null --> G1(t),
 t::tree<val_32_1082,children_32_1083>@M * 
  G2(children_32_1083,n_1104@NI,t@NI)&children_32_1083!=null & 
  n_1104=null --> G1(t)]


*/
