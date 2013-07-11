data tree {
    //int val; 
    node children;
    }
    
data node {
    tree child; 
    //node prev; 
    node next; 
    tree parent;
    }

treep<> == 
  self::tree<c>* c::dll<self> ;

dll<parent> == 
  self=null or 
  self::node<c,n,parent>*c::treep<>* n::dll<parent>;

  //self=null or

HeapPred H1(tree a).
PostPred G1(tree a).
HeapPred H2(node a,tree@NI b).
PostPred G2(node a,tree@NI b).

/*
 H2(l,prv,par)<--> l::node<child_07,prev_08,next_09,parent_10> * 
     H1(child_07) * H_2(prev_08,prv,par) * H2(next_09,l,par) * H_4(parent_10,prv,par)
     or l=null

 H1(t) <-> t::tree<children> & children=null
      or t::tree<children> * H2(children,n_38',t) & n_38'=null & children!=null 
*/


bool check_tree (tree t)
  requires t::treep<>@L ensures res;
//  infer [H1,G1,H2,G2] requires H1(t) ensures G1(t) & res;
{
   //node n = null;
   if (t.children==null) return true;
   else return check_child(t.children,t); 
    //check_child(t.children,t,t); // (node * tree * tree)
}

bool check_child (node l, tree par)
  requires l::dll<par>@L ensures  res;
//infer [H1,G1,H2,G2] requires H2(l,par) ensures G2(l,par) & res;
{
	if (l==null) return true;
	else if (l.parent==par) 
           return check_child(l.next, par)&& check_tree(l.child);
	else return false;
}

/*
# check-mcf-2.ss

  H2(l,prv,par)&
  l!=null --> l::node<child_07,prev_08,next_09,parent_10>@M * 
  H_1(child_07,prv,par) * 
  H_2(prev_08,prv,par) * 
  H_3(next_09,prv,par) * H_4(parent_10,prv,par).

 H_3(next_09,prv,par)&par=par' & 
  prev_08=prv --> H2(next_09,l,par).

 H_1(child_07,prv,par)&par=par' & 
  prev_08=prv --> H1(child_07).

 H_2(prev_08,prv,par) --> emp&
  forall(parent_10:((par!=parent_10 | prv>=prev_08)) & 
  ((par!=parent_10 | prev_08>=prv))).

 H_2(prev_08,prv,par) --> emp&
  forall(parent_10:((prev_08!=prv | par>=parent_10)) & 
  ((prev_08!=prv | parent_10>=par))).

 H_2(prev_08,prv,par) --> emp&
  forall(parent_10:((par>=parent_10 | prv>=prev_08)) & 
  ((parent_10>=par | prv>=prev_08)) & ((par>=parent_10 | 
  prev_08>=prv)) & ((parent_10>=par | prev_08>=prv))).

 H1(t) --> t::tree<val_83,children_84>@M * 
  H_5(children_84).

 H_5(children_84)&
  children_84!=null --> H2(children_84,n_38',t).

---------

 H2(l,prv,par)&l=null --> G2(l,prv,par).

 H_5(children_84) * t::tree<val_83,children_84>@M&
  children_84=null --> G1(t).

 H_2(prev_08,prv,par) * 
  H_4(parent_10,prv,par) * 
  l::node<child_07,prev_08,next_09,parent_10>@M * 
  G2(next_09,l,par) * G1(child_07)&par=parent_10 & 
  prev_08=prv --> G2(l,prv,par).

 t::tree<val_83,children_84>@M * 
  G2(children_84,n_1105,t)&children_84!=null & 
  n_1105=null --> G1(t).


*/
