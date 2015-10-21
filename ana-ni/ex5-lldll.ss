data node{
//        int val;
        node prev;
        node next;
}


relation R(node x).
relation P(node x).


void paper_fix (node x, node p)
  infer [@ana_ni,R,P]
  requires R(x) & P(y)
  ensures true;
{
  if (x!=null) 
    {
      x.prev=p;
      paper_fix(x.next,x); 
    }
}


/*
*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [R]: ( R(x)) -->  x!=1,
RELDEFN P: ( true) -->  P(y_1718),
RELDEFN R: ( 2<=v_node_20_1695') -->  R(v_node_20_1695')]
*************************************


 */
