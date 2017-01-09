struct node{
//        int val;
  struct node* prev;
  struct  node* next;
};

/*@
ll<> == self = null  or self::node< _ , q> * q::ll<>;
dll<p> == self = null or self::node< p , q> * q::dll<self>;   // p stores the prev node
*/
/*@
HeapPred H1(node a, node@NI b).
PostPred G1(node a, node@NI b).
*/
void paper_fix (struct node* x, struct node* p)
//@ infer[H1,G1] requires H1(x,p) ensures G1(x,p);
// requires x::ll<> ensures x::dll<p>;
{
        if (x!=NULL) 
        {
            x->prev=p;
            //@ dprint;
            paper_fix(x->next,x); 
        }
}
