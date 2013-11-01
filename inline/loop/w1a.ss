 data node {
  int val;
  node  next;
}

ll<> == self=null
  or self::node<_,p>*p::ll<>;

HeapPred H( node a).
HeapPred G( node a).


int main(node l)
  requires l::ll<>
  ensures true;
{

  int i=0;

  while (true)
      requires l::ll<>
      ensures l'=null ; //& flow __break_;
    /*
    infer [H,G]
      requires H(l)
      ensures G(l');//'
    */
    {
      if (l==null) break;
      l = l.next;
      i++;
  }

  return i;
}
