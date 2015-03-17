data node {
  int val;
  node next;
}

ll<> == (self:ll1)=null   // has to detect that ll1 is not a type
  inv true;

ll1<> == self=null
  or self::node<_,_>
  inv true;
