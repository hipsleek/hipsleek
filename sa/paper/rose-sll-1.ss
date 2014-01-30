data tree {
    int val; 
    node children;
    }
    
data node {
    tree child; 
    node next; 
    tree parent;
    }

HeapPred H1(tree a).
PostPred G1(tree a).
HeapPred H2(node a,tree@NI b).
PostPred G2(node a,tree b).
/*
treep<> == 
  self::tree<_,c>* c::sll<self> ;

sll<parent> == 
  self=null or 
  self::node<c,n,parent>*c::treep<>* n::sll<parent>;
*/
bool check_tree (tree t)
/*
requires t::treep<> //& t!=null 
  ensures res;
 */
  infer [H1,H2,G1,G2]
  requires H1(t) //t::treep<>@L //& t!=null 
  ensures G1(t) & res;
{
   if (t.children==null) return true;
   else return check_child(t.children,t); 
}

bool check_child (node l, tree par)
/*
 requires l::dll<par, prev> 
  ensures  res;
 */
  infer [H1,H2,G1,G2]
  requires H2(l,par) //l::sll<par>@L 
  ensures  G2(l,par) & res;
{
	if (l==null) return true;
	else if (l.parent==par) return check_child(l.next, par)&& check_tree(l.child);
	else return false;
}

/*
# rose-sll-1.ss 

This is a simpler rose-tree with sll

We currently perform inference of each method separately.
However, for mutual recursive methods; we must perform the
fix-point simulatenously. That is use Hoare rule to first
gather the two sets of assumptions.

After that, combine them into a single set for shape
inference.

[ HP_979(children_29_978) * t::tree<val_29_977,children_29_978>@M&
  children_29_978=null --> G1(t),
 H1(t) --> t::tree<val_29_977,children_29_978>@M * HP_979(children_29_978),
 HP_979(children_29_978) * t::tree<val_29_977,children_29_978>@M&
  children_29_978!=null --> H2(children_29_978,t),
 G2(children_29_978,t)&children_29_978!=null --> G1(t)]

*******relational definition ********
*************************************
[ H1(t_999) ::= t_999::tree<val_29_977,children_29_978>@M&children_29_978=null,
 G1(t_1000) ::= 
 t_1000::tree<val_29_977,children_29_978>@M&children_29_978=null
 or G2(children_29_978,t_1000)&children_29_978!=null
 ]

Procedure check_tree$tree SUCCESS

Checking procedure check_child$node~tree... 
*************************************
*******relational assumptions (4) ********
*************************************
[ H2(l,par)&l=null --> G2(l,par),
 H2(l,par)&
  l!=null --> l::node<child_39_1008,next_39_1009,parent_39_1010>@M * 
  HP_1011(child_39_1008,par@NI) * HP_1012(next_39_1009,par@NI) * 
  HP_1013(parent_39_1010,par@NI) * HP_1014(par,l@NI),
 HP_1012(next_39_1009,par@NI) * HP_1013(par',par@NI) * HP_1014(par,l@NI)&
  par=par' --> H2(next_39_1009,par),
 HP_1011(child_39_1008,par@NI)&par=par' --> H1(child_39_1008),
 l::node<child_39_1008,next_39_1009,par>@M * 
  G2(next_39_1009,par) --> G2(l,par)]

*******relational definition ********
*************************************
[ H1(t_999) ::= t_999::tree<val_29_977,children_29_978>@M&children_29_978=null,
 G1(t_1000) ::= 
 t_1000::tree<val_29_977,children_29_978>@M&children_29_978=null
 or G2(children_29_978,t_1000)&children_29_978!=null
 ,
 G2(l_1068,par_1069) ::= 
 emp&l_1068=null
 or l_1068::node<child_39_1008,next_39_1009,par_1069>@M * 
    G2(next_39_1009,par_1069)
 ,
 HP_1014(par,l) ::= NONE,
 HP_1011(child_39_1008,par) ::= NONE,
 HP_1013(parent_39_1010,par) ::= NONE,
 H1(a) ::= NONE]
*************************************


*/
