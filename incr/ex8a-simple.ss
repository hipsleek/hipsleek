/* Build a list of the form 1->...->1->0 */

data node {
 int h;
 node next;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

//HeapPred H(node x, node b). // non-ptrs are @NI by default
//  PostPred G(node x,  node b,  node c, node d). // non-ptrs are @NI by default

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x,  node b).

ll_one<> == self=null
  or self::node<1,q>*q::ll_one<>
  ;

lseg_one<p> == self=p
  or self::node<1,q>*q::lseg_one<p>
  ;


void create_one (ref node p, ref node t)

//infer [H,G] requires H(p)   ensures G(p,p');

  requires p::lseg_one<_> ensures p'::lseg_one<_> ; //'
{
  if (bool_nondet()) {
    t = new_node();
    t.h = 1;
    t.next = p;
    p = t;
    create_one(p,t);
  }
}


/* void main() */

/* { */
/*   node a = new_node(); */
/*   node p =a; */
/*   bool flag = true; */
/*   bool r; */

/*   create_one_two(p,flag); */
/*   p.h = 3; */

/*   flag = true; */
/*   /\* */
/*   r = check_one_two_ok(p,flag); */
/*    assert (r); */
/*   *\/ */
/*   r = check_one_two_fail(p,flag); */
/*   assert (!r); */
/* } */
