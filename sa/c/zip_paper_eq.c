struct node{
  int val;
  struct node * next;
};
/*@
ll<> == self = null  or self::node^<_, q> * q::ll<>;

ltwo<p:node__star> == p=self & self = null  
   or self::node^<_, q> * p::node^<_,r> * q::ltwo<r>;
lthree<p:node__star,r:node__star> == p=r &r=null & self = null  
   or self::node^<_, q1> * p::node^<_,q2> * r::node^<_,q3> * q1::lthree<q2,q3>;

HeapPred H(node__star a, node__star b).
PostPred G(node__star a, node__star b, node__star c).
*/

struct node* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::node^<_,_>;
  }
*/;


struct node* zip (struct node* x, struct node* y)
/*@
  infer [H,G]
  requires H(x,y)
  ensures  G(x,y,res);
*/
//requires x::ltwo<y>  ensures x::lthree<y,res>;
{
   if (x==NULL){
     if (y==NULL)
       return x;
     else{
/*@
       assume false;
*/
       return x;
     }
   }
   else {
     struct node* tmp =  malloc(sizeof(struct node));
      tmp->val = x->val+y->val;
      tmp->next = zip(x->next,y->next);
      return tmp;
      // return new node(x->val+y->val, zip(x->next,y->next));
   }
}
