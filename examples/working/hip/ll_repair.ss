data node {
	node next;	
}

// HeapPred P(node y).
// HeapPred Q(node y).

// node fcode(node y)
//   // infer[P,Q]
//   requires P(y)
//   ensures Q(y);

ll<n> == self = null & n = 0
	or self::node<q> * q::ll<n-1> 
  inv n >= 0;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null 
  ensures x::ll<n1+n2>;
{
  // x::ll<n1> * y::ll<n2> & x != null
  // <=> x = null * y::ll<n2> & n = 0 & x != null
  // \/ exists q. x::node<q> * q::<n1-1> * y::ll<n2> & n1 > 0 & x != null
  // <=> exists q. x::node<q> * q::<n1-1> * y::ll<n2> & n1 > 0 & x != null
	if (x.next == null){
// exists q. x::node<q> * q::<n1-1> * y::ll<n2> & n1 > 0 & x != null & q = null
// <=> x::node<q> * y::ll<n2> & n1 > 0 & x!=null & q = null
// <=> x::node<q> * y = null & n1 > 0 & x!= null & q = null & n2 = 0
// \/ exists k. x::node<q> * y::node<k> * k::ll<n2-1> & x!= null & q = null & n1 > 0 & n2 > 0
	      //x.next = y.next; // x.next = y;
        // F |- P(y)
        //x.next = fcode(y);
        x.next = y;

        // F & Q(y, x.next) |- post(append)
// x::node<q> * y = null & n1 > 0 & x!= null & q = null & n2 = 0 |- exists m. y -> node{m}.
        }
	else {
	 	append(x.next, y);
    }
}

// (1) x::node<q> * y::ll<n2> & n1 > 0 & x!=null & q = null & n1=1 |- P(y)
// (2) x::node<q> * y::ll<n2> & n1 > 0 & x!=null & q = null & n1=1 & Q(y,x.next) |- x::ll<n1+n2>

// (1) x::node<q> * y::ll<n2> & q = null |- P(y)
// P(y) is a pre-condition
// ==> find the weakest pre-condition
// ==> true


// Q(y,res) is a post-condition
// ==> find the strongest post-condition
// (2) x::node<q> * y::ll<n2> & q = null & Q(y,x.next) |- x::ll<1+n2>     (unroll rhs, match x::node<q>)
// ==> y::ll<n2> & q = null & Q(y,x.next) & x.next=q |- q::ll<n2>         (match y::ll<..>)
// ==> q = null & Q(y,x.next) & x.next=q |- y=q
// ==> q = null & Q(y,x.next) |- y=x.next

// ==> Q(y,x.next) := y=x.next
// ==> Q(y,res) := res=y
