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

// coercion "lseg2" self::ls<p, n> <- self::ls<q, n1> * q::ls<p, n2> & n=n1+n2;

  
node source(node n)
requires n::node<_,q>
ensures res::node<v,q> & v<0 & n=res;
/*
{
	if(n != null)
	{
		n.val = -1;
	}
	return n;
}
*/

void sink(node n)
requires n::node<v,q> & v >0
ensures n::node<v,q>;
{
	if(n !=null)
	{
		if(n.val <= 0) assert false;
		/*
		/* node n is tainted */
		if(n.val == 0) /* may be tainted */
		if(n.value >0) /* node n is not tainted */ */
	}
}

node sanitizer(node n)
requires n::node<v,q> 
ensures res::node<w,q> & w>0 & n=res;
/*
{
	if(n !=null)
	{
		if(n.val <= 0)
			n.val = 1; /*sanitized user input */
	}
	return n;
}
*/

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

requires x::ls<p,m> * p::node<a,null>
ensures x::ls<p,m> * p::node<a,null> & res=p;

{
        //if (x==null) assert false;

	if( x.next != null)
                { //assume false;
		  return ret_last(x.next);
			
                 }
	return x;
}

 void set_next(node x, node y)

	requires x::node<a,_> 
	ensures x::node<a,y> ;

{
	x.next = y;
}


node ret_first(node x)

	requires x::ls<p,m> * p::node<a,nn>
	ensures x::ls<p,m> * p::node<a,nn> & res = p;

{
	return x;
}

/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<n1> * y::ll<n2> & n1>0 // & x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
  
  requires x::ls<null,n> & n > 0
  ensures x::ls<y,n>;
  
  requires x::ls<p,n> * p::node<a,null> 
  ensures x::ls<p,n> * p::node<a,y>;

{
  //assume false;
   //assert x=null;
	if (x.next == null)
	  { //dprint;
        x.next = y;
        //dprint;
      }
	else
      { 
        //node z;
        //z = null;
        //dprint;
		append(x.next, y);
      }
    }
	
	node get_next_next(node x) 

	requires x::ll<n> & n > 1
	ensures res::ll<n-2>;
	
	requires x::node<v1,q1>*q1::node<v2,q2>
	ensures x::node<v1,q1>*q1::node<v2,q2> & res = q2;

{
	return x.next.next;
}
void basictest1()
requires true
ensures true;
{
	node n1 = new node(0,null);
	n1 = source(n1);
	n1 = sanitizer(n1); 
	sink(n1); /*should be error without call to sanitizer first*/
}

void basictest2()
requires true
ensures true;
{
	node n1 = create_list(10);
	n1 = source(n1);
	n1 = sanitizer(n1);
	sink(n1);	/* Good */
	// sink(n1.next);	/* Bad */
}



void basictest3()
requires true
ensures true;
{	
	node n1 = create_list(10);
	node n2 = new node(0,null);
	n2 = source(n2);
	//dprint;
    //assert n1'::ls<null,pp> & pp>0;
	insert(n1, n2.val);
	node n3 = ret_last(n1);
	n3 = sanitizer(n3);
	sink(n3); /*Tainted through n2*/
}

void basictest4()
requires true
ensures true;
{
	node n1 = new node(0,null);
	node n2 = new node(0,null);
	n2 = source(n2);
	set_next(n1,n2);
	n1.next = sanitizer(n1.next);
	sink(n1.next); /*Tainted through n2 */
}

void basictest5()
requires true
ensures true;
{
	node n1 = new node(0,null);
	node n2 = new node(0,null);
	node n3 = new node(0,null);
	n2 = source(n2);
	n3 = source(n3);
	set_next(n1,n2);
	node t = n1.next;
	//dprint;
	n1.next = sanitizer(t);
	set_next(n2,n3);
	t = n2.next;
	n2.next = sanitizer(t);
	node n4 = ret_last(n1);
	sink(n4); /*Tainted through n2 */
}



void test1()
requires true
ensures true;
{
	node l1 = new node(0,null);
	node n1 = new node(0,null);
	n1 = source(n1);
	insert(l1, n1.val);
	node n2 = ret_first(l1);
	n2 = sanitizer(n2);
	sink(n2); 
}

void test2()
requires true
ensures true;
{
	node l1 =  create_list(10);
	node l2 =  create_list(10);
	node n1 =  new node(0,null);
	n1 = source(n1);
	insert(l1, n1.val);
	node n2 = sanitizer(n1);
	insert(l2,n2.val);
	//sink(ret_last(l1));
	sink(ret_last(l2));
}
void test3()
requires true
ensures true;
{	
	node l1 =  create_list(10);
	node l2 =  create_list(10);
	node n1 =  new node(0,null);
	
	n1 = source(n1);
	n1 = sanitizer(n1);
	insert(l1,n1.val);
	append(l2,l1);
	id3(l2);
	sink(ret_last(l2));
}
void id3(node z)
requires z::ls<p,a> * p::ls<q,b>
ensures z::ls<q,a+b> ;

void test4(node n)
{
	node l1 =  create_list(2);
	node l2 =  create_list(2);
	node n1 =  new node(0,null);
	n1 = source(n1);
	n1 = sanitizer(n1);
	insert(l1,n1.val);
	append(l1,l2);
	//id3(l1);
	sink(l1.next.next);
}
/*
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<n1> * y::ll<n2> & n1>0 // & x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;

{
  //assume false;
   //assert x=null;
	if (x.next == null)
	  { //dprint;
        x.next = y;
        //dprint;
      }
	else
      { 
        node z;
        z = null;
        dprint;
		append(x.next, y);
      }
    }

/* return the first element of a singly linked list */
node ret_first(node x)

	requires x::ll<n> * y::ll<m> & n < m 
	ensures x::ll<n>;

{
	return x;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n> & n > 0
	ensures x::ll<1> * res::ll<n-1>; 

{
	node tmp = x.next;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j> & i > 0 
	ensures x::ll<j+1>; 

{
	x.next = y;
}



/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n> & n > 1
	ensures res::ll<n-2>;

{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<n> & n > 0 
	ensures x::ll<n+1>;

{
			//dprint;
      node tmp = null;
	
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
	requires x::ll<n> & n > a & a > 0 
	ensures x::ll<n - 1>;
{
        if (a == 1)
	{
		//node tmp = x.next.next;
		//x.next = tmp;
                  x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}


/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 
	ensures res::ll<a>;

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

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<n+m> & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse(xs, ys);
	}
}

node ret_last(node n)
	requires x::ll<n> * y::ll<m> & n < m 
	ensures x::ll<n>;

{
	if( n.next != null)
		ret_last(n.next);
	else return n;
}


void basictest1()
{
	node n1 = create_list(10);
	n1 = source(n1);
	/* n1 = sanitizer(n1); */ 
	sink(n1); /*should be error without call to sanitizer first*/
}

void basictest2()
{
	node n1 = create_list(10);
	n1 = source(n1);
	n1 = sanitizer(n1);
	sink(n1);	/* Good */
	sink(n1.next);	/* Bad */
}

void basictest3()
{	
	node n1 = create_list(10);
	node n2 = new node(0,null);
	n2 = source(n2);
	n1.insert(n2, n2.val);
	node n3 = ret_last(n1);
	sink(n3); /*Tainted through n2*/
}

void basictest4()
{
	node n1 = new node(0,null);
	node n2 = new node(0,null);
	n2 = source(n2);
	n1.set_next(n2);
	sink(n1.next); /*Tainted through n2 */
}

void test1()
{
	node l1 = new node(0,null);
	node n1 = new node(0,null);
	n1 = source(n1);
	l1.insert(n1, n1.val);
	node n2 = l1.ret_first();
	sink(n2); 
}

void test2()
{
	node l1 =  create_list(10);
	node l2 =  create_list(10);
	node n1 =  new node(0,null);
	n1 = source(n1);
	l1.insert(n1, n1.val);
	node n2 = sanitizer(n1);
	l2.insert(n2,n2.val);
	sink(l1.ret_last());
	sink(l2.ret_last());
}

void test3()
{	
	node l1 =  create_list(10);
	node l2 =  create_list(10);
	node n1 =  new node(0,null);
	n1 = source(n1);
	l1.insert(n1, n1.val);
	append(l2,l1);
	sink(l2.ret_last());
}
void test4(node n)
{
	node l1 =  create_list(2);
	node l2 =  create_list(2);
	node n1 =  new node(0,null);
	n1 = source(n1);
	l1.insert(n1, n1.val);
	append(l1,l2);
	sink(l1.get_next_next());
}

*/