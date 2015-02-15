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
  
lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

node append3(node x, node y)
  requires x::lseg<null,n> & Term[n] 
  ensures res=y & x=null & n=0// n=0
  or res::lseg<y,m> & res=x & x!=null & m=n & n>0; //m>0
{
  if (x==null) return y;
  //dprint;
  node tmp=x.next;
  //assume tmp'=null or tmp'!=null;
  x.next = append3(tmp,y);
  return x;
}


/* append two singly linked lists */
void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null & Term[n1] // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 & Term[n1] // & x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)

	requires x::ll<n> * y::ll<m> & n < m & Term 
	ensures x::ll<n>;

{
	return x;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n> & n > 0 & Term
	ensures x::ll<1> * res::ll<n-1>; 

{
  //dprint;
	node tmp = x.next;
    //assume false;
	x.next = null;
	return tmp;
}


/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j> & i > 0 & Term 
	ensures x::ll<j+1>; 

{
	x.next = y;
}

void set_null2(node x)

	requires x::ll<i> & i > 0 & Term 
	ensures x::ll<1>;

{
	if (4>3) 
		x.next = null;
	else 
		x.next = null;
}	


/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<i> & i > 0 & Term 
	ensures x::ll<1>;

{
	x.next = null;
    //dprint;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n> & n > 1 & Term
	ensures res::ll<n-2>;

{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<n> & n > 0 & Term[n] 
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
	requires x::ll<n> & n > a & a > 0 & Term[n] 
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

/*node delete1(node x, int a)
	requires x::ll1<S>  
	ensures res::ll1<S1> & ((a notin S | S=union(S1, {a})) | S = S1);
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}*/

/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 & Term[a] 
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

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
	requires xs::ll<n> * ys::ll<m> & Term[n] 
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
