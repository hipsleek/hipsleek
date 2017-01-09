struct node{
//        int val;
  struct node* prev;
  struct  node* next;
};

/*@
ll<> == self = null  or self::node< _ , q> * q::ll<>;
dll<p> == self = null or self::node< p , q> * q::dll<self>;   // p stores the prev node
*/

void paper_fix (struct node* x, struct node* p)
// requires x::ll<> ensures x::dll<p>;
{
        if (x!=NULL) 
        {
            x->prev=p;
            paper_fix(x->next,x); 
        }
}
