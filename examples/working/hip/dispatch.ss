/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

ll3<n,sum> == self = null &  n = 0 &  sum=0  
  or self::node<v, q> * q::ll3<n1, sum1> & v>=0 & n=1+n1 &
  sum=sum1+v 
  inv n>=0 & sum>=0;

ll3a<n,"s":sum> == self = null 
  &  n = 0 & ["s": sum=0]  // false when "B" missing 
  or self::node<v, q> * q::ll3a<n1, sum1> & v>=0 & n=1+n1 &
  ["s": sum=sum1+v]
  inv true & n>=0 & ["s": sum>=0 ];



/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

llsum<n> == self = null & n = 0 
	or self::node<v, q> * q::llsum<n-v>;

llS<S> == self = null // & S = {} 
	or self::node<v, q> * q::llS<S1> & S = union(S1, {v});

llH<n,"s":sum,"B":B> == self = null 
  &  n = 0 & ["s": sum=0]  // false when "B" missing 
  or self::node<v, q> * q::llH<n1, sum1,B1> & v>=0 & n=1+n1 &
  ["s": sum=sum1+v ; "B":B=union(B1,{v})]
  inv true & n>=0 & ["s": sum>=0 ];

	
void dispatch(node lst, ref node gtl, ref node ltl)
/*
  requires lst::ll3<n,s> 
  ensures gtl'::ll3<n1,s1> * ltl'::ll3<n2,s2> 
  & n=n1+n2 & s=s1+s2 & s1>=3*n1 & s2 <= 2*n2 ;// s2<3*n2+1 ; 
*/
  requires lst::llS<B> 
  ensures gtl'::llS<B1> * ltl'::llS<B2> 
     & B=union(B1,B2) 
     & forall (x:(x notin B1 | x>=3))
    & forall (y:(y notin B2 | y<3)); 

{
  if (lst == null) {
     gtl=null; 
     ltl =null;
     }
   else {
     node tmp = lst.next;
     node gt; node lt;
     if (lst.val>=3) {
          dispatch(tmp,gt,lt);         
          lst.next = gt;
          gtl = lst;
          ltl=lt;
     } else {
          dispatch(tmp,gt,lt);
          lst.next = lt;
          ltl = lst;
          gtl=gt;
     }
   }
}


	
/*
ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});

/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<n1> * y::ll<n2> & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<m> & m=n1+n2;

{
  //assume false;
   assert x=null;
	if (x.next == null)
	  { //dprint;
        x.next = y;
        //dprint;
      }
	else
      { 
        node z;
        z = null;
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

void set_null2(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	if (2>1) 
		x.next = null;
	else 
		x.next = null;
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




