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


/*
treep<> == 
  self::tree<c>* c::dll<self> ;

dll<parent> == 
  self=null or 
  self::node<c,n,parent>*c::treep<>* n::dll<parent>;
*/


treep<> == 
  self::tree<c>* c::dll<self> ;

dll<parent> == 
  self=null or 
  self::node<c,n,parent>*c::tree<cc>* cc::dll<c>* n::dll<parent>;

treep2<> == 
  self::tree<c>* c::dll2<self> ;

dll2<parent> == 
  self=null or 
  self::node<c,n,parent> * n::dll2<parent>
  * c::tree<cc>* cc::dll2<c> 
  ;

treep3<> == 
  self::tree<c> & c=null or
  self::tree<c>* c::dll3<self> & c!=null ;

dll3<parent> == 
  self=null or 
  self::node<c,n,parent> * n::dll3<parent>
  * c::tree<cc>* cc::dll3<c> 
  ;

treep4<> == 
  self::tree<c> & c=null or
  self::tree<c>* c::dll4<self> & c!=null ;

dll4<parent> == 
  self=null 
  or self::node<c,n,parent> * n::dll4<parent>
  * c::tree<cc> & cc=null
  or self::node<c,n,parent> * n::dll4<parent>
  * c::tree<cc>* cc::dll4<c> & cc!=null
  ;

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
//requires t::treep4<> ensures t::treep4<> & res;
//requires t::treep4<>@L ensures res;//fail
//requires t::treep3<>@L ensures res;//fail
//requires t::treep2<>@L ensures res; //fail
//requires t::treep<>@L ensures res;
//requires t::treep<> ensures t::treep<> & res;
infer [H1,G1,H2,G2] requires H1(t) ensures G1(t) & res;
{
   //node n = null;
   if (t.children==null) return true;
   else return check_child(t.children,t); 
    //check_child(t.children,t,t); // (node * tree * tree)
}

bool check_child (node l, tree par)
//requires l::dll4<par> ensures  l::dll4<par> & res; // cannot prove post
//requires l::dll4<par>@L ensures  res;//pre fail
// requires l::dll3<par>@L ensures  res;//fail
//  requires l::dll2<par>@L ensures  res;//fail
//requires l::dll<par>@L ensures res;
//requires l::dll<par> ensures  l::dll<par> & res;
infer [H1,G1,H2,G2] requires H2(l,par) ensures G2(l,par) & res;
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

======================================
HeapPred H65(node cc4).
HeapPred H93(node next90, tree@NI par).
HeapPred H92(tree child89, tree@NI par).
HeapPred H1(tree a).
HeapPred H2(node a, tree@NI b).
PostPred G1(tree a).
PostPred G2(node a, tree@NI b).
HeapPred H94(tree parent91, tree@NI par).

[ // BIND
  H1(t) --> t::tree<cc4>@M * H65(cc4),
 // PRE_REC
  H65(cc4)&
   cc4!=null |#| t::tree<cc4>@M --> H2(cc4,t@NI),
 // POST
  H65(cc4) * t::tree<cc4>@M
     &cc4=null --> G1(t),
 // POST
  t::tree<cc4>@M * G2(cc4,t@NI)&
cc4!=null --> G1(t)]

=====

  H2(l,par@NI)& l!=null --> 
    l::node<child89,next90,parent91>@M * 
    H92(child89,par@NI) * H93(next90,par@NI) * 
    H94(parent91,par@NI),
  // PRE_REC
  H93(next90,par@NI)&par=parent91 
    --> H2(next90,par@NI),
  // PRE_REC
  H92(child89,par@NI)&par=parent91 --> H1(child89),
  // POST
  H2(l,par@NI)&l=null --> G2(l,par@NI),
  // POST
  H94(parent91,par@NI) * l::node<child89,next90,par>@M 
  * G2(next90,par@NI) * G1(child89)&
   par=parent91 --> G2(l,par@NI),
  // POST
  H94(parent91,par@NI)&par=parent91 --> emp]

[ G1(t1) ::=  t1::tree<cc4>@M&cc4=null
         or t1::tree<cc4>@M * G2(cc4,t1)&cc4!=null
 ,
 G2(l2,par3) ::=  
     emp&l2=null
    or l2::node<child89,next90,par3>@M * 
        G2(next90,par3) * child89::tree<cc4>@M& cc4=null
    or l2::node<child89,next90,par3>@M * G2(next90,par3) * 
        child89::tree<cc4>@M * G2(cc4,child89)&cc4!=null
 ,
 H1(t_1078) ::= t_1078::tree<cc4>@M * H2(cc4,t_1078)&cc4!=null
     or t_1078::tree<cc4>@M&cc4=null
 ,
 H2(l_1109,par0) ::= 
     H2(next_9,par0) * l_1109::node<child_0,next_9,par0>@M * 
       child_0::tree<cc4>@M&cc4=null 
     or H2(next_9,par0) * l_1109::node<child_0,next_9,par0>@M 
      * child_0::tree<cc4>@M * H2(cc4,child_0) & cc4!=null 
     or emp&l_1109=null
 ]
*/
