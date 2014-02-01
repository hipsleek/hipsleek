struct  node{
  int val;
  struct node* next;
};

/*@
HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).
*/

/*
  lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;

*/


void lscan( struct node*@R cur, struct node*@R prev, struct node* sent)
/*
  requires cur::node<_,n> * n::lx<_,sent> * prev::lx<_,sent> & cur!=sent
// ensures prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures prev'::node<_,p> * p::lx<_,sent> & cur'=sent ;//'
*/
/*
requires cur::node<_,n> * n::lx<_,sent> * prev::lx7<_,sent>
// ensures prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures prev'::node<_,p> * p::lx7<_,sent> & cur'=sent ;//'
*/
/*@
  infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);
*/
{

  struct node* n;
  n = cur->next;
  // rotate ptrs
  cur->next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
    return;
  }
  if (cur == NULL) {
      // change direction;
      cur = prev;
      prev = NULL;
  }
  lscan(cur,prev,sent);

}

