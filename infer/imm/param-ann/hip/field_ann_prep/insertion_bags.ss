/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});

ll_b<S> == self = null & S = {}
	or self::node<v, q> * q::ll_b<S1> & S = union(S1, {self});

sll1<S> == self=null & S={}
	or self::node<v, r> * r::sll1<S1>  & S=union(S1, {v}) & 
	forall (x: (x notin S1 | v <= x));

/*sorted linked list*/
sll_b<S, mi, ma > == self::node<mi, null> & mi = ma & S = {self}
	or self::node<mi, q> * q::sll_b<S1, k, ma>  & S = union(S1, {self}) & mi <= k
  inv mi <= ma;

lemma "L1" self::sll_b<S, mi, ma> -> self::ll_b<S>;

/* function to insert an element in a sorted list */
node insert(node x, node vn)
  requires x::sll_b<S, mi, ma> * vn::node<v, _>
//  ensures res::ll_b<_>;
  ensures res::sll_b<_, _, _> ;//& S1 = union(S, {vn});
                                             //  ensures res::sll_b<S1, min(mi,v), max(ma,v)> & S1 = union(S, {vn});
{
  if (x.next == null) {
    x.next = vn;
    vn.next = null;
    return x;
  }else{
    if (vn.val <= x.val){
      vn.next = x;
      return vn;
    } else {
        x.next = insert (x.next, vn);
        dprint;
        return x;
      } 
  }
}

int length(node x)
  requires x::sll_b<S, mi, ma> 
  ensures  x::sll_b<S, mi, ma>;

{
  if (x.next == null) return 1;
  else return  1 + length(x.next);
}

/*   if (x.next == null){ */
/*     x.next = vn;  */
/*     vn.next = null;  */
/*     return x; */
/*   }	else { */
/*     if (vn.val <= x.val){  */
/*       vn.next = x;  */
/*       return vn;  */
/*     } */
/*     else */
/*       { */
/*         x.next = insert(x.next, vn); */
/*         return x; */
/*       } */
/*   } */
/* } */

/* insertion sort */
/*void insertion_sort(node x, ref node y)
	requires x::ll1<S1> * y::sll1<S2>
	ensures y'::sll1<S> * x::ll1<S1> & S = union(S1, S2);

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}


*/
