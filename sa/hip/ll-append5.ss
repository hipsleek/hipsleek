data node {
  int val;
  node next;
}


HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H2(node a,node b).

//HeapPred G1(node a, node b, node c).

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


  infer[H2,G2]
  requires H2(x,y)
  ensures G2(x,y);

/*
PROBLEM : base case for G2(x,y)?
 Would recursion at HP_577 be a problem for 
 the non-recursive H2?

!!! HP_577([v_node_36_594])
!!!  =:  
 emp&v_node_36_594=null
 or v_node_36_594::node<val_36_558',next_36_559'> * HP_577(next_36_559')&true
 
!!! >>>>>> generalize_one_hp: <<<<<<
!!! G2([x,y])
!!!  =:  x::node<val_36_585,v_node_36_600> * G2(v_node_36_600,y)&v_node_36_600!=null
!!! >>>>>> generalize_one_cs_hp: <<<<<<
!!! H2([x,y])= x::node<val_36_558',next_36_559'> * HP_577(next_36_559')&true
!!! >>>>>> equivalent hp: <<<<<<

   */

{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

