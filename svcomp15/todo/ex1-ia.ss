

data node {
  int val;
  node next;
}

HeapPred H(node a, int b).
PostPred G(node a, int b, int c).

int NewNode(node x, int a)

//  infer [H,G] requires H(x,a) ensures G(x,res,a);
/*   requires true */
/*   ensures case { */
/*    a>=0 -> [] res::node<0,null>; */
/*    a<0 -> [] res = null; */
/* }; */
{
  if (a < 0) x=null;

  return x.val;
}

/*

void main(int x)
// requires true ensures true;
{
  node tmp = new node(x,null);
  int t = NewNode(tmp, 1);

  return;
}
*/

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



