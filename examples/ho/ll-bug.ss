/*

  [fix]

  Bug:
  - The send assertion should fail.

 */

data node {
  int val; 
  node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
  or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void clone(node l, ref node ol)
  requires l::ll<n> & n>=0 & ol=null
  ensures l::ll<n> * ol'::ll<n>; //'
{
  if (l==null){
    ol = null;
  }else{
    node nol = null;
    clone(l.next,nol);

    assert nol'=null; //fail here, CORRECT

    ol =  new node(l.val, nol);

    assert nol'=null; //' but ok here, BUG
    //SHOULD FAIL here
  }
}
