/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next; //#REC;	
}



/*
lemma_unsafe "lseg" self::node<_,q1>*q1::lseg<p> 
    <-> self::lseg<q>*q::node<_,p>;
*/

clist<> == selfe ::node<_,q>*q::lseg<self>;

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

HeapPred P(node x).
HeapPred P2(node x,node y).


clist2<> == 
  self::node<_,q>*q::lseg<self>
  or self::lseg<q2>*q2::node<_,self>;
  
clist3<> == self::node<_, q> * P2(q, self);

//clist2<> --> self::node<_,q>*q::lseg<self>;
//clist2<> <-- self::lseg<q2>*q2::node<_,self>;

//lemma_safe "cir" self::clist<> -> self::clist2<>.

int len_seg(node x)
  infer [P2,@classic]//@pure_field]
  requires P2(x,p) //x::node<_, q> * P2(q, x)
  ensures false;
{    
  if (x==null) return 0;
  else { 
    node n = x.next;
    //dprint;
    int r=len_seg(n);
    //dprint;
    return 1+r;
  }
}

/*
# ex20e9a.ss -dre "infer_collect_hp_rel"

 infer [P,Q] P(x)*Q(y) |- x::node<_,ys>
      P(x)->x@I


*/
