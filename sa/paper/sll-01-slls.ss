data node_low {
    node_low next;
}

data node_top {
    node_top next;
    node_low data_;
}


node_top create_top()
  requires true
  ensures res::node_top<null,null>;
{
  node_top ptr = new node_top(null, null);
  return ptr;
}

node_low create_low()
  requires true
  ensures res::node_low<null>;
{
  node_low ptr = new node_low(null);
   
    return ptr;
}

bool get_nondet()
  requires true
  ensures true;

 node_top alloc()
  requires true
   ensures res::node_top<null,l> & l=null
   or res::node_top<null,l> * l::node_low<null>;
{
    node_top pi = create_top();
    if (get_nondet())
        pi.data_ = create_low();

    return pi;
}

ll<> == self = null
  or self::node_top<p, r> * p::ll<> & self != null  & r=null
  or self::node_top<p, r> * p::ll<> * r::node_low<null> & self != null;

HeapPred H(node_top a).
node_top helper ()
 /* requires true */
 /*  ensures res::ll<>; */
 infer[H]
 requires true
  ensures H(res);
{
  node_top tmp, x;
  if (get_nondet()) return null;
  else {
    tmp = helper();
    x = alloc();
    x.next = tmp;
    return x;
  }
}

/*
 node_top create_sll(node_top x)
{
    node_top sll = alloc();
    node_top *now = sll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
        now->next = alloc();
        now = now->next;
    }

    return sll;
}
*/
