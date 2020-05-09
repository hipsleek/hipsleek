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
 requires head_ref::node_star<v> * v::ll<n>
  ensures head_ref::node_star<v1> * v1::ll<n + 1>;
*/
{
   struct node* newNode = (struct node*) malloc(sizeof(struct node));
   newNode -> data = data;
   newNode -> next = *head_ref;
   *head_ref = newNode;
}

void addLast(struct node** head_ref, int data) {
   struct node* newNode = (struct node*) malloc(sizeof(struct node));
   newNode -> data = data;
   newNode -> next = NULL;

   if (*head_ref == NULL) {
       *head_ref = newNode;
   } else {
       struct node* ptr = *head_ref;
       while (ptr -> next != NULL) ptr = ptr -> next;
       ptr -> next = newNode;
   }
}

void freeList(struct node* head) {
   struct node* p1 = head;
   struct node* p2;
   while (p1 != NULL) {
       p2 = p1;
       p1 = p1 -> next;
       free(p2);
   }
}

void printList(struct node* ptr) {
   printf("List:\n");
   while (ptr != NULL) {
       printf("%d\n", ptr -> data);
       ptr = ptr -> next;
   }
}

// Memory Leak Example
int main() {
   struct node* head = NULL;
   addLast(&head, 1);
   addFirst(&head, 0);
   // 2. if also comment out the printList() line,
   // which accesses the structure in a loop,
   // error can be found even with --unroll 1 in SMACK
   printList(head);
   // 1. if only comment out the freeList() line,
   // no error reported by SMACK unless with --unroll 3 or more
   // freeList(head);
   return 0;
}
