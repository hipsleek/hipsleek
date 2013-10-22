
struct node {
  int val;
  struct node* next;
} _node;
/*@
ll<> == self=null
  or self::node^<_,p>*p::ll<>;

 */

void foo(struct node* x)
/*@
 requires x::ll<>
 ensures  x::ll<>;
*/
 {
   if (x != NULL) {
     foo(x->next);
   }
   return;
 }

