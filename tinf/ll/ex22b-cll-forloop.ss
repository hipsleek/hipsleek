data node {
  int val;
  node next;
}

pred lseg<p,n> ==
   self=p & n=0
  or self::node<_,q>*q::lseg<p,n-1>
 inv n>=0;


void forloop(ref int i, int n, ref node curr)
  requires curr::node<_,_> & i<=n & Term[n-i]
  ensures  curr::lseg<curr',m>*curr'::node<_,_> & i'=n & i'>=i & m=n+i;
{
  if (i>=n) return;
  else {
    node next_node = new node();
    next_node.val = i;
    curr.next = next_node;
    curr = next_node;
    i = i+1;
    forloop(i,n,curr);
  }
}

/*
//Initialize a circular linked list with length n
node_t* init_cll (int n)
// requires emp
// ensures res::clist<>
{
  node_t* head;
  node_t* curr = alloca(sizeof(node_t));
  
  curr->val = 0;
  head = curr;
  // head::node<0,null> & curr=head

  for (int i = 1; i < n; i++) 
    // requires curr::node<_,null>
    // ensures  curr::lseg<curr'>*curr'::node<_,null>
  {
    node_t* next_node = alloca(sizeof(node_t));
    next_node->val = i;
    curr->next = next_node;
    curr = next_node;
  }
  
  curr->next = head;
}
*/
