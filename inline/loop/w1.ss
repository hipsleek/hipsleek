 data node {
  int val;
  node  next;
}

ll<> == self=null
  or self::node<_,p>*p::ll<>;

HeapPred H( node a).
  HeapPred G( node a,node b).


int main(node l)
  requires l::ll<>
  ensures l::ll<>;
{

  int i=0;

  while (l !=null)
      requires l::ll<>
      ensures l::ll<> & l'=null;
    /*
    infer [H,G]
      requires H(l)
      ensures G(l,l');//'
    */
    {
      l = l.next;
      i++;
  }

  return i;
}
