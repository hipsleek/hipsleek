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

treep<> == 
  self::tree<_,c>* c::dll<self,null> ;

dll<parent, prev> == 
  self=null or 
  self::node<c,prev,n,parent>*c::treep<>* n::dll<parent,self>;

  //self=null or

HeapPred H1(tree a).
PostPred G1(tree a).
HeapPred H2(node a,node@NI c,tree@NI b).
PostPred G2(node a,node@NI c,tree@NI b).

/*
 H2(l,prv,par)<--> l::node<child_07,prev_08,next_09,parent_10> * 
     H1(child_07) * H_2(prev_08,prv,par) * H2(next_09,l,par) * H_4(parent_10,prv,par)
     or l=null

 H1(t) <-> t::tree<children> & children=null
      or t::tree<children> * H2(children,n_38',t) & n_38'=null & children!=null 

dll<parent, prev> == 
  self=null or 
  self::node<c,prev,n,parent>* n::dll<parent,self>
    * c::tree<_,cc>* cc::dll<c,null> ;

*/

 
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
 infer [H1,G1,H2,G2] requires H2(l,prv,par) ensures G2(l,prv,par) & res;
{
  if (l==null) return true;
  else if (l.parent==par && l.prev==prv)
    return check_child(l.next,l, par)&& check_tree(l.child);
  else return false;
  /* if (l==null) return true; */
  /* else   */
  /*   return (l.parent==par && l.prev==prv)  && check_child(l.next,l, par)&& check_tree(l.child); */
}

/*

check-mcf.ss --pred-en-equiv

Why are post-conditions printed before precondition?
Where is the definition of G2? Why is it circular?
Why aren't G1 & H1 made equal. 

[ G1(t_1189) ::=children_48_1077::G2<n_1099,t_1189>@M * 
  t_1189::tree<val_48_1076,children_48_1077>@M&n_1099=null,
 G2(l_1186,prv_1187,par_1188) ::=l_1186::G2<prv_1187,par_1188>@M,
 H1(t_1161) ::=t_1161::tree<val_48_1076,children_48_1077>@M * 
  children_48_1077::G2<n_38',t_1161>@M&n_38'=null,
 H2(l_1183,prv_1184,par_1185) ::=l_1183::G2<prv_1184,par_1185>@M]

check-mcf.ss --pred-unify-inter

[ G1(t_1189) ::= G2(children_48_1077,n_1099,t_1189) * 
t_1189::tree<val_48_1076,children_48_1077>@M,
 G2(l_1186,prv_1187,par_1188) ::= 
 l_1186::node<child_60_999,prv_1187,next_60_1001,par_1188>@M * 
 G2(next_60_1001,l_1186,par_1188) * 
 G2(children_48_1077,n_1099,child_60_999) * 
 child_60_999::tree<val_48_1076,children_48_1077>@M
 or emp&l_1186=null
 ,
 H1(t_1161) ::= t_1161::tree<val_48_1076,children_48_1077>@M * 
H2(children_48_1077,n_38',t_1161),
 H2(l_1183,prv_1184,par_1185) ::= 
 emp&l_1183=null
 or H2(next_60_1124,l_1183,par_1185) * 
    l_1183::node<child_60_1122,prev_60_1123,next_60_1124,parent_60_1125>@M * 
    child_60_1122::tree<val_48_1076,children_48_1077>@M * 
    H2(children_48_1077,n_38',child_60_1122)&prev_60_1123=prv_1184 & 
    par_1185=parent_60_1125
 ]

# check_tree

HeapPred H5(node n1, node@NI prv, tree@NI par).
HeapPred H3(tree c9, node@NI prv, tree@NI par).
HeapPred H4(node p0, node@NI prv, tree@NI par).
HeapPred H6(tree par2, node@NI prv, tree@NI par).
HeapPred H1(tree a).
HeapPred H2(node a, node@NI c, tree@NI b).
HeapPred HP_1078(node ch77).
PostPred G2(node a, node@NI c, tree@NI b).
PostPred G1(tree a).

[ // BIND
 H1(t) --> t::tree<val_48_1076,ch77>@M * HP_1078(ch77),
 // PRE_REC
 HP_1078(ch77)&n_38'=null & ch77!=null |#| 
    t::tree<val_48_1076,ch77>@M --> H2(ch77,n_38'@NI,t@NI),
 // POST
(1;0)HP_1078(ch77) * t::tree<val_48_1076,ch77>@M&ch77=null --> G1(t),
 // POST
(2;0)t::tree<val_48_1076,ch77>@M * G2(ch77,n_1099@NI,t@NI)&n_1099=null 
     & ch77!=null --> G1(t)]


[ // BIND(2;0)
 H2(l,prv@NI,par@NI)& l!=null --> l::node<c9,p0,n1,par2>@M
  * H3(c9,prv@NI,par@NI) * H4(p0,prv@NI,par@NI) * H5(n1,prv@NI,par@NI) 
  * H6(par2,prv@NI,par@NI),
 // PRE_REC(1;2;0)
  H5(n1,p0@NI,par@NI)&p0=prv & par=par2 |#| 
     l::node<c9,p0,n1,par>@M --> H2(n1,l@NI,par@NI),
 // PRE_REC (1;2;0)
  H3(c9,p0@NI,par@NI)&p0=prv & par=par2 --> H1(c9),
 // POST(1;0)
  H2(l,prv@NI,par@NI)& l=null --> G2(l,prv@NI,par@NI),
 // POST(1;2;0)
  H4(p0,prv@NI,par@NI) * H6(par2,prv@NI,par@NI) 
  * l::node<c9,p0,n1,par>@M * G2(n1,l@NI,par@NI) 
  * G1(c9)&p0=prv & par=par2 --> G2(l,p0@NI,par@NI)]

============== older version ===============

# check-mcf.ss

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
