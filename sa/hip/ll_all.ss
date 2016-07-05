/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
  HeapPred H3(node a, node b, node c).
/* append two singly linked lists */
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).

/*
void append2(node x, node y)
  infer [H2,G2]
  requires H2(x,y)
  ensures G2(x,y);

HP_599(y_598,y) ::= 
 emp&y_598=y
 or y_598::node<val_42_572,y_602> * HP_599(y_602,y)&true
 ,
H2(x,y) ::= x::node<val_42_547',next_42_548'> * HP_604(next_42_548',y) * HP_597(y)&true,
 HP_RELDEFN G2
G2(x,y) ::= x::node<val_42_572,y_598> * HP_599(y_598,y) * HP_596(y)&true]

Possible answer:
 First obtain:
  H2(x,y) == x::node<_,nil> * P1(y)
    or x::node<_,q> * H2(q,y)
  G2(x,y) == x::node<_,y> * P1(y)
    or x::node<_,q> * G2(x,y)

 Then derive:
  H2(x,y) == x::node<_,q> * P2(q,y)
  P2(x,y) == P1(y) & x=nil
    or x::node<_,q> * H2(q,y)
  G2(x,y) == x::node<_,q> * P3(q,y)
  P3(x,y) == P1(y) & x=y
    or x::node<_,q> * P3(q,y)

        H2(x,y) == x::node<_,q> * P2(q,y)
        P2(x,y) == P1(y) & x=nil
          or x::node<_,q> * H2(q,y)
        G2(x,y) == x::node<_,q> * P3(q,y)
        P3(x,y) == P1(y) & x=y
          or x::node<_,q> * P3(q,y)

   H2(x,y) == x::node<_,q> * P2(q,y) & P1(y)
   P2(x,y) == x=nil
     or x::node<_,q> * P2(q,y)
   G2(x,y) == x::node<_,q> * P3(q,y) * P1(y)
   P3(x,y) == x=y
      or x::node<_,q> * P3(q,y)
 
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}
*/

void append(ref node x, node y)
  infer [H2,G3]
  requires H2(x,y)
  ensures G3(x,x',y); //'
{
	if (x == null)
	      x = y;
	else 
		append(x.next, y);
}

/*
// return the first element of a singly linked list 
node ret_first(node x)

	requires x::ll<n> * y::ll<m> & n < m 
	ensures x::ll<n>;

{
	return x;
}

// return the tail of a singly linked list 
node get_next(node x)

	requires x::ll<n> & n > 0
	ensures x::ll<1> * res::ll<n-1>; 

{
  //dprint;
	node tmp = x.next;
    //assume false;
	x.next = null;
	return tmp;
}


// function to set the tail of a list 
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j> & i > 0 
	ensures x::ll<j+1>; 

{
	x.next = y;
}

void set_null2(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	if (4>3) 
		x.next = null;
	else 
		x.next = null;
}	


// function to set null the tail of a list 
void set_null(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	x.next = null;
    //dprint;
}

// function to get the third element of a list 
node get_next_next(node x) 

	requires x::ll<n> & n > 1
	ensures res::ll<n-2>;

{
	return x.next.next;
}

// function to insert a node in a singly linked list 
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

node delete1(node x, int a)
	requires x::ll1<S>  
	ensures res::ll1<S1> & ((a notin S | S=union(S1, {a})) | S = S1);
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}

node create_list(int a)
	requires a >= 0 
	ensures res::ll<a>;

{
	node tmp;

	if (a == 0) {
      // assume false;
		return null;
	}
	else {    
		a  = a - 1;
        //    dprint;
		tmp = create_list(a);
        //    dprint;
		return new node (0, tmp);
	}
		
}

void reverse(ref node xs, ref node ys)
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<n+m> & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
		xs = tmp;
    //dprint;
		reverse(xs, ys);
	}
}
*/
/*
void reverse1(ref node xs, ref node ys)
	requires xs::ll1<S1> * ys::ll1<S2> 
	ensures ys'::ll1<S3> & S3 = union(S1, S2) & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse1(xs, ys);
	}
}*/
/*
void test(node x)
	requires x::ll<n> & n>=2 ensures x::ll<n-1>;
{
	node tmp = x.next.next;
	x.next = tmp;
}
*/




