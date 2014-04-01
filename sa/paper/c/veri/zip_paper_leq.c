struct node{
  int val;
  struct node* next;
};
#include "../../../../examples/working/cparser/stdhip.h"

struct node* alloc()
/*@
 requires true
  ensures res::node<_,_> ;
*/
{
   return malloc(sizeof(struct node));
}

/*@
ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> ==  self = null  or self::node<_, q> * p::node<_,r> * q::ltwo<r>;
lthree<p:node,r:node> == r=null & self = null  or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;
*/
/*@
HeapPred H(node a, node b).
HeapPred G(node a, node b, node c).
*/
struct node* zip (struct node* x, struct node* y)
// infer [H,G]  requires H(x,y)  ensures  G(x,y,res);
//@ requires x::ltwo<y>  ensures x::lthree<y,res>;
{
   if (x==NULL) return x;
   else 
   {
   // assume false;
   int v = x->val+y->val;
   struct node* n = alloc();
   n->next = zip(x->next,y->next);
   n->val = v;
   return n;//new node(v,n);
   }
}

/*
# hip zip_paper_leq.ss --sa-en-sp-split --pred-en-dangling --en-texify > a
*************************************
*******relational definition ********
*************************************
[ \seppred{H}{x_914,y_915} ::=  
 \seppred{H}{next_22_899,next_22_897} * 
 \sepnode{y_915}{node}{val_22_896,next_22_897} * 
 \sepnode{x_914}{node}{val_22_898,next_22_899}
 or \seppred{HP_864}{y_915}&x_914=null
 ,
 \seppred{G}{x_918,y_919,res_920} ::=  
 \sepnode{x_918}{node}{val_22_834,next_22_835} * 
 \sepnode{y_919}{node}{val_22_841,next_22_842} * 
 \seppred{G}{next_22_835,next_22_842,v_node_22_868} * 
 \sepnode{res_920}{node}{v_int_22_867,v_node_22_868}&v_int_22_867=val_22_841+
 val_22_834
 or \seppred{HP_864}{y_919}&res_920=x_918 & x_918=null & res_920=null
 ]
*************************************
*******relational assumptions (4) ********
*************************************
 \seppred{HP_864}{y}&res=x & x=null & res=null --> \seppred{G}{x,y,res},
 \seppred{H}{x,y}&x=null --> \seppred{HP_864}{y},
 \seppred{H}{x,y}&x!=null --> \sepnode{x}{node}{val_22_834,next_22_835} * 
  \seppred{HP_836}{next_22_835,y@NI} * \seppred{HP_837}{y,x@NI},
 \seppred{HP_837}{y,x@NI} --> \sepnode{y}{node}{val_22_841,next_22_842} * 
  \seppred{HP_843}{next_22_842,x@NI},
 \seppred{HP_836}{next_22_835,y@NI} * 
  \seppred{HP_843}{next_22_842,x@NI} --> \seppred{H}{next_22_835,next_22_842},
 \sepnode{x}{node}{val_22_834,next_22_835} * 
  \sepnode{y}{node}{val_22_841,next_22_842} * 
  \seppred{G}{next_22_835,next_22_842,v_node_22_868} * 
  \sepnode{res}{node}{v_int_22_867,v_node_22_868}&v_int_22_867=val_22_841+
  val_22_834 --> \seppred{G}{x,y,res}]
-------------





--sa-en-sp-split performs split during entailment
and generate continuation HP_864(y) for base-case:

[ HP_864(y)&res=x & x=null & res=null --> G(x,y,res),
 H(x,y)&x=null --> HP_864(y),
                   ^^^^^^^^^
 H(x,y)&x!=null --> x::node<val_22_834,next_22_835>@M * 
  HP_836(next_22_835,y@NI) * HP_837(y,x@NI),
 HP_837(y,x@NI) --> y::node<val_22_841,next_22_842>@M * 
  HP_843(next_22_842,x@NI),
 HP_836(next_22_835,y@NI) * 
  HP_843(next_22_842,x@NI) --> H(next_22_835,next_22_842),
 x::node<val_22_834,next_22_835>@M * y::node<val_22_841,next_22_842>@M * 
  G(next_22_835,next_22_842,v_node_22_868) * 
  res::node<v_int_22_867,v_node_22_868>@M&v_int_22_867=val_22_841+
  val_22_834 --> G(x,y,res)]


 */
