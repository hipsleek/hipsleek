//Ex.5: Memory Leak

struct node {
   int data;
   struct node* next;
};

/*@
pred ll<n> == self = null & n = 0
           or self::node<_, q> * q::ll<n-1>
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


void addFirst(struct node** head_ref, int data)
/*@
 requires head_ref::node_star<v> 
  ensures head_ref::node_star<q> * q::node<v,data>;
*/
{
   struct node* newNode = (struct node*) malloc(sizeof(struct node));
   newNode -> data = data;
   newNode -> next = *head_ref;
   *head_ref = newNode;
}

