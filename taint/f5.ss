data Node {
  int val;
  Node next;
}

same_ll<other> ==
  self=null & other=null
  or self::Node<v,n1>*other::Node<v,n2>*n1::same_ll<n2>
  inv true;

//lemma_safe self::same_ll<y> <-> self::same_ll<x>;

// Simple Example
void foo(Node l1, Node l2, Node h1, Node h2)
  requires l1!=null
  ensures l1!=null;
{
  assume l1::same_ll<l2>;
  l1.val = 5;
  l2.val = 5;
  must_assert l1::same_ll<l2>;
}

