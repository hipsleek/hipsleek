 data node {
  int val;
  node  next;
}

ll<> == self=null
  or self::node<_,p>*p::ll<>;

void while_loop(node@R l,int i)
  requires l::ll<>
  ensures l::ll<> & l'=null;
{
  if (l!=null) {
         l = l.next;
         i++;
         while_loop(l,i);
  }
}

int main(node l)
  requires l::ll<>
  ensures true;
{

  int i=0;

  while_loop(l,i);

  return i;
}
