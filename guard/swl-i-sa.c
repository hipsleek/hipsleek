struct node {
  int val;
  struct node* next;
};

/*@
ll<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::ll<s> & self!=s 
inv self!=s ;
*/

/*@
lseg<p> == self=p 
  or self::node<_,nxt> * nxt::lseg<p> & self!=p 
inv true;
*/

/*@
lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=g & self!=s 
 inv self!=s ;
*/

/*@
HeapPred H(node a, node b, node@NI c).
HeapPred H1(node a, node@NI c).
HeapPred H2(node a, node@NI c).
PostPred G(node a, node ra, node b, node rb, node@NI c).
*/

void lscan(struct node* cur, struct node* prev, struct node* sent)
{
  struct node* n;
  n = cur->next;

  cur->next = prev;

  prev = cur;
  cur = n;

  while (cur != sent)
  /*@
    infer [H,G]
    requires H(cur,prev,sent)
    ensures G(cur,cur',prev,prev',sent);
  */
  {
    if (cur == NULL) {
      cur = prev;
      prev = NULL;
    }
  }

  return;
}
