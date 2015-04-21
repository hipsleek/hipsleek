

data node {
  int val;
  node next;
}

GG<m> ==
 case { m>=0 -> [] self::node<0,null>;
        m<0 -> [] self = null;
};

PostPred G(node a, int b).

node NewNode(int a)
//  requires true ensures res::GG<a>;
  infer [G] requires emp &true ensures G(res,a);
/*   requires true */
/*   ensures case { */
/*    a>=0 -> [] res::node<0,null>; */
/*    a<0 -> [] res = null; */
/* }; */
{
  node x = null;
  if (a >=0) x=new node(0,null);

  return x;
}


void main()
 requires true ensures true;
{
  node tmp = NewNode(1);
  tmp.val = 0;

  return;
}


/*

requires true
ensures
 res_1409::node<v_int_20_1411,v_null_type_20_1408>&0<=a_1410 &
 v_null_type_20_1408=null
 or emp&a_1410<0 & res_1409=null


==>
requires true
ensures
 case 0<=a_1410 --> res_1409::node<v_int_20_1411,v_null_type_20_1408>&0<=a_1410 &
 v_null_type_20_1408=null;
 a_1410<0 ->  emp&a_1410<0 & res_1409=null;

 */



