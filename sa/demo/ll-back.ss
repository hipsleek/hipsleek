data node {
  node next;
}

ll1<> == self::node<q> * q::ll1<>
  inv true;

ll<> == self = null
	or self::node<q> * q::ll<>
  inv true;

HeapPred H1(node a).
HeapPred G1(node b).

node malloc(int s)
  requires true
  ensures res::node<_> or res=null;

int for_aux( node@R ptr)

// requires ptr::ll<>
//  ensures ptr'::ll<>;//'

//  ensures false;

  infer[H1,G1]
  requires H1(ptr)
  ensures G1(ptr'); //'

{
  node old_ptr = ptr;
  //ptr = new node(old_ptr);
  ptr = malloc(1);
  if (ptr==null) {
    ptr = old_ptr;
    //dprint;
    return -1;
  }

  ptr.next = old_ptr;
  for_aux(ptr);
  return 0;
}

HeapPred H2(node a).
HeapPred G2(node b).

int main(node@R ptr)

              /* requires true */
              /* ensures ptr'::ll<>;//' */


  infer [G2]
  requires true
  ensures G2(ptr');//'

{
   ptr = null;
  for_aux(ptr);

  return 0;
}

             /*
[ // PRE_REC
(2;0) H1(ptr) * ptr'::node<old_31'>@M & old_31'=ptr --> H1(ptr'),
 // POST
(1;0) H1(ptr) & ptr=ptr' --> G1(ptr'),
 // POST
(2;0) G1(ptr') --> G1(ptr')]
             */
