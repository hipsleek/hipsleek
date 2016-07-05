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


void test3(bool b)
requires true
ensures true;
{	
	node n1 = create_list(10);
	node n2 = new node(0,null);
	//n2 = source(n2);
	//n2 = sanitizer(n2);
    dprint;
    int i;
    { 
      //dprint; // four states visible which seems wrong..
      assert i'=0; //' default to norm; once but incorrect
    }
}

/*
[Label: []
 State:es_formula: 
        EXISTS(w_443: (166, ):n1_56'::ll<v_int_159_415> * 
        (162, ):n2_57'::node<w_443,q_436> & v_int_159_415=10 & 
        v_int_160_416=0 & v_ptr_160_417=null & q=v_ptr_160_417 & 
        (144, ):v_439<0 & v=v_439 & q_436=q & (160, ):0<w_443 &
        {FLOW,(27,28)=__norm,})
       es_pure: true
       es_heap: true
       es_path_label: [((34, ):,6 );((36, ):,1 );((37, ):,7 );((24, ):,-1 )]],
Failed States:
[]
Successful States:
[Label: []
 State:es_formula: 
        EXISTS(w_451: (174, ):n1_56'::ls<flted_72_426,v_int_159_427> * 
        (170, ):n2_57'::node<w_451,q_444> & v_int_159_427=10 & 
        (139, ):flted_72_426=null & v_int_160_428=0 & v_ptr_160_429=null & 
        q=v_ptr_160_429 & (152, ):v_447<0 & v=v_447 & q_444=q & 
        (168, ):0<w_451 & {FLOW,(27,28)=__norm,})
       es_pure: true
       es_heap: true
       es_path_label: [((34, ):,6 );((36, ):,1 );((37, ):,8 );((24, ):,-1 )]]

*/
