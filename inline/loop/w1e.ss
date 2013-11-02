 data node {
  int val;
  node  next;
}

ll<> == self=null
  or self::node<_,p>*p::ll<>;


int main(node l)
  requires l::ll<>
  ensures true;
{

  int i=0;
  while (true)
   requires l::ll<>
   ensures l::ll<> & l'=null or l::ll<> & l'=null & flow __RET;
  {
    if (l==null) return;
    l = l.next;
    i++;
  }
}
