data node {
  int val;
  node next;
}


HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H1a(node a).
HeapPred H2(node a, node b).
HeapPred HP1(node a, node b).

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void append(node x, node y)

  infer[H1,H1a,G2]
  requires H1(x) * H1a(y)
     ensures G2(x,y) * H1a(y);

  /*
[ HP_RELDEFN HP_619
HP_619(next_54_618) ::=next_54_618::ll[LHSCase]&true,
 HP_RELDEFN HP_612
HP_612(y_611,y) ::=y_611::lseg<y>[LHSCase]&true,
 HP_RELDEFN H1a
H1a(y) ::=htrue&true,
 HP_RELDEFN H1
H1(x) ::=x::node<val_54_617,next_54_618> * 
  next_54_618::ll[LHSCase]&true,
 HP_RELDEFN G2
G2(x,y) ::=x::node<val_54_610,y_611> * 
  y_611::lseg<y>[LHSCase]&true]

   */
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

