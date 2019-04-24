data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

node insert_last(node x , int a)
  requires x::ls<null,n> & n=0 ensures res::ls<null,1>;
  requires x::ls<null,n> & n>0 ensures x::ls<null,n+1> & res=x;
{
  if (x == null) {
    node u = new node(a, null);
    return x;
  }
  else if (x.next == null) {
    node u = new node(a, null);
    return x;
  }
  else {
    insert_last(x.next, 1);
    return x;
  }
}
