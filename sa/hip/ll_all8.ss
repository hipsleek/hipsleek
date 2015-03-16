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

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).


void set_null2(node x)
    infer [H1,G1]
	requires H1(x)
	ensures G1(x);
    /*
!!! HP_573([next_33_581])= HP_583(next_33_581)&true
[ HP_583(next_33_581) ::=UNKNOWN,
 G1(x_585) ::= x_585::node<val_33_582,next_33_550'>&next_33_550'=null,
 H1(x_584) ::= x_584::node<val_33_549',next_33_550'> * HP_583(next_33_550')&true]

Should be: same with ll_all9.ss
 H1(x)=x::node<_,q>* P(q)
 G1(x)=x::node<_,null>*P(q)
     */
{
	if (4>3) 
		x.next = null;
	else 
		x.next = null;
}	



/*


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




