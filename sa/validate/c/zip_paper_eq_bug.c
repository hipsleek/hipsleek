#include "../../../examples/working/cparser/stdhip.h"
//#include<stdio.h>
//#include<stdlib.h>

typedef struct node node;
struct node {
   int val;
   node* next;
};

/*@ 
ll<> == self = null  
    or self::node<_, q> * q::ll<>;

ltwo<p:node> == p=self & self = null  
   or self::node<_, q> * p::node<_,r> * q::ltwo<r>;

lthree<p:node,r:node> == p=r &r=null & self = null  
   or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;
*/
/*@
HeapPred H(node a, node b).
PostPred G(node a, node b, node c).
*/

node* zip (node* x, node* y)
//@ infer [H,G]  requires H(x,y)  ensures  G(x,y,res);
// requires x::ltwo<y>  ensures x::lthree<y,res>;
{
   if (x==NULL) 
	{
		if (y==NULL) return x;
		else 
		{
                  //@ assume false;
		  return x;
		}
	}
   else {
     node* tmp = malloc(sizeof(node));
     tmp->val=x->val+y->val;
     tmp->next=zip(x->next,y->next);
     return tmp;
   }
}

int main() {
  return 0;
}


