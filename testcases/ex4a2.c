//Ex.5: Memory Leak

struct node {
   int data;
   struct node* next;
};

/*@
pred ll<n> == self = null & n = 0
           or self::node<_, q> * q::ll<n-1>
   inv n >= 0;

pred lseg<n,q> == self = q & n=0
           or self::node<_, q> * q::lseg<n-1,q>
   inv n >= 0;
*/

struct node *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::node<_, _>;
  }
*/;


void addFirst(struct node** head_ref, int d1)
/*@
  requires head_ref::node_star<v> 
  ensures head_ref::node_star<q> * q::node<d1,v>;
  requires head_ref::node_star<v> * v::ll<m>
  ensures head_ref::node_star<v1> * v1::ll<m + 1>;
*/
{
   struct node* newNode = (struct node*) malloc(sizeof(struct node));
   newNode -> data = d1;
   newNode -> next = *head_ref;
   *head_ref = newNode;
}

void addLast(struct node** head_ref, int d1)
/*@
   requires head_ref::node_star<null>
   ensures  head_ref::node_star<q> * q::node<_,null>;
   requires head_ref::node_star<q> * q::lseg<n,r> * r::node<_,null>
   ensures  head_ref::node_star<q> * q::lseg<n,r> * r::node<_,s> *s::node<d1,null>;
*/
{
   struct node* newNode = (struct node*) malloc(sizeof(struct node));
   newNode -> data = d1;
   newNode -> next = NULL;

   if (*head_ref == NULL) {
       *head_ref = newNode;
   } else {
       struct node* ptr = *head_ref;
       while (ptr -> next != NULL)
         /*@
           requires ptr::lseg<n,q>*q::node<_,null>
           ensures  ptr::lseg<n,q>*q::node<_,null> & ptr'=q;
          */
          ptr = ptr -> next;
       ptr -> next = newNode;
   }
}
