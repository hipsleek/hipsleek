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


void addFirst(struct node** head_ref, int d1)
/*@
  requires head_ref::node_star<v> 
  ensures head_ref::node_star<q> * q::node<d1,v>;
  requires head_ref::node_star<v> * v::ll<n>
  ensures head_ref::node_star<v1> * v1::ll<n + 1>;
*/
{
   struct node* newNode = (struct node*) malloc(sizeof(struct node));
   newNode -> data = d1;
   newNode -> next = *head_ref;
   *head_ref = newNode;
}

