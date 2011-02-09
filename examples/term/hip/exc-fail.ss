/* singly linked lists */

/* representation of a node */

data node {
	int val; //>0 means untainted
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

ull<n> == self = null & n = 0 
	or self::node<v, q> * q::ull<n-1> & v>0 
  inv n >= 0;
	
ls<p,n> == self = p & n = 0 
	or self::node<_, q> * q::ls<p,n-1> 
  inv n >= 0;


node source(node n)
requires n::node<_,q>
ensures res::node<v,q> & v<0;

void sink(node n)
requires n::node<v,q> & v >0
ensures n::node<v,q>;


node sanitizer(node n)
requires n::node<v,q> 
ensures res::node<w,q> & w>0;


/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 
	ensures res::ll<a>;
	requires a >= 0
	ensures res::ls<null,a>;
{
	node tmp;

	if (a == 0) {
		return null;
	}
	else {
		a  = a - 1;
		tmp = create_list(a);
		return new node (0, tmp);
	}
		
}


/* function to insert a node in a singly linked list */
void insert(node x, int a)
	//requires x::ll<n> & n > 0 
	//ensures x::ll<n+1>;

	//requires x::ull<n> & n > 0 & a>0 
	//ensures x::ull<n+1>;

	 requires x::ls<null,n> & n > 0 
	 ensures x::ls<p,n> * p::node<a,null>;

{
			//dprint;
      node tmp = null;
	
	if (x.next == null)
	{
		
		x.next = new node(a, tmp);


	}
	else { 
              
		insert(x.next, a);
             }
} 

node ret_last(node x)

requires x::ls<p,n> * p::node<a,null>
ensures x::ls<p,n> * p::node<a,null> & res=p;

{
        //if (x==null) assert false;

	if( x.next != null)
                { //assume false;
		  return ret_last(x.next);
			
                 }
	return x;
}


// assert ..; & assert .. assume ..; - for normal flow
// assert_catch  ..; // what is visible to catch
// assert_return ..; // what is visible to a return

// dprint        // what is visible to normal
// dprint_catch  // what is visible to catch
// dprint_all    // what is visible to return
// if already fail should indicate 
//    those failures already occurred

void test2(node x, bool b) 
  requires x::ll<n>
  ensures true;
{
  int i;
  if (x==null) {
    i=1;
    x.val=3;
  } else {
    i=2;
    x.val=3;
  }
  dprint;
}


