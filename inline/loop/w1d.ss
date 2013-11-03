 data node {
  int val;
  node  next;
}

ll<> == self=null
  or self::node<_,p>*p::ll<>;

void skip()
 requires true
  ensures true;

void while_loop(node@R l,int i)
  requires l::ll<>
  ensures l::ll<> & l'=null;
{
  if (true) {
    try {
         if (l==null) raise new __Exc(); // change to __Break
         l = l.next;
         i++;
         while_loop(l,i);
    } catch (__Exc e) {
         skip();
    };
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
