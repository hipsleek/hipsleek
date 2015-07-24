/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

void dispose(node x)
  requires x::node<_,_>
  ensures true;


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q1> * q1::node<_, q2> * q2::ll<n-2> 
  //inv exists (k: n = 2*k & k >= 0)
  inv n>=0
  ;


/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

/* append two singly linked lists */
void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null & n1=5 // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1=5 // & x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{
	if (x.next == null)
	  x.next = y;
	else 
	  append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)

	requires x::ll<n> & n= 7
	ensures x::ll<n>;

{
	return x;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n> & n =5
	ensures x::ll<1> * res::ll<n-1>; 

{
  //dprint;
	node tmp = x.next;
    //assume false;
	x.next = null;
	return tmp;
}

//not terminated

/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j> & i =11
	ensures x::ll<j+2>;

{
	x.next.next = y;
}


/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<i> & i =11
	ensures x::ll<1>;

{
	x.next = null;
    //dprint;
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
	requires x::ll<n> & n =15
	ensures x::ll<n+2>;
{
			//dprint;
      node tmp = null;
      if (x.next.next == null){
          tmp = new node(a, null);
          x.next.next = new node(a, tmp);
      }
      else
        insert(x.next.next, a);
} 




/*****************************************/
/*********SMALLROOT EXAMPLES*************/



/*function to remove the first node which has value v in singly linked list*/
void list_remove(node x, int v)
        requires x::ll<n> & n =9// & x.val != v
        ensures x::ll<m> & m <= n;
{
        if(x.next != null) {
                   if(x.next.val == v) {
                            node tmp = x.next;
                            x.next = x.next.next;
                            dispose(tmp);
                   }
                   else {
                            list_remove(x.next, v);
                   }
        }
}
