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

/* append two singly linked lists */
/*
void append2_f(node x, node y)
  requires x::ll<n1> * y::ll<n2> //& n1>0
  ensures x::ll<m> & m=n1+n2;
{
  if (x.next == null)
    x.next = y;
  else
    append2(x.next, y);
}
*/
void append2(node x, node y)
  infer[n1]
  requires x::ll<n1> * y::ll<n2> //& n1>0
  ensures x::ll<m> & m=n1+n2;
{
  if (x.next == null)
    x.next = y;
  else
    append2(x.next, y);
}
/*
void append_f(node x, node y)
  requires x::ll<n1> * y::ll<n2> //& n1>0
  ensures x::ll<n1+n2>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}
*/
void append(node x, node y)
   infer[n1]
  requires x::ll<n1> * y::ll<n2> //& n1>0
  ensures x::ll<n1+n2>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)
	requires x::ll<n>
	ensures x::ll<n>;
{
	return x;
}

/* return the tail of a singly linked list */
/*
node get_next_f(node x)
  requires x::ll<n> //& n > 0
  ensures x::ll<1> * res::ll<n-1>;
{
	node tmp = x.next;
	x.next = null;
	return tmp;
}
*/
node get_next(node x)
  infer[n]
  requires x::ll<n> //& n > 0
  ensures x::ll<1> * res::ll<n-1>;
{
  //dprint;
	node tmp = x.next;
    //assume false;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
/*
 void set_next_f(node x, node y)
 //   infer[i]
   requires x::ll<i> * y::ll<j>// & i > 0
   ensures x::ll<j+1>;
{
	x.next = y;
}
*/
 void set_next(node x, node y)
   infer[i]
   requires x::ll<i> * y::ll<j> //& i > 0
   ensures x::ll<j+1>;
{
	x.next = y;
}
/*
void set_null2_f(node x)
  requires x::ll<i> //& i > 0
  ensures x::ll<1>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}
*/
void set_null2(node x)
  infer[i]
  requires x::ll<i> //& i > 0
  ensures x::ll<1>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
/*
void set_null_f(node x)
  requires x::ll<i> //& i > 0
  ensures x::ll<1>;
{
	x.next = null;
}
*/
void set_null(node x)
  infer[i]
  requires x::ll<i> //& i > 0
  ensures x::ll<1>;
{
	x.next = null;
}

/* function to get the third element of a list */
/*
node get_next_next_f(node x)
  requires x::ll<n> //& n > 1
  ensures res::ll<n-2>;
{
	return x.next.next;
}
*/
node get_next_next(node x)
  infer[n]
  requires x::ll<n> //& n > 1
  ensures res::ll<n-2>;
{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
/*
void insert_f(node x, int a)
  requires x::ll<n> //& n > 0
  ensures x::ll<n+1>;
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}
*/
void insert(node x, int a)
  infer[n]
  requires x::ll<n> //& n > 0
  ensures x::ll<n+1>;
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

/* function to delete the a-th node in a singly linked list */
/*
void delete_f(node x, int a)
  requires x::ll<n> //& n > a & a > 0
  ensures x::ll<n - 1>;
{
  if (a == 1){
    x.next = x.next.next;
  }
  else{
    delete(x.next, a-1);
  }
}
*/
//todo: ??
/*
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EBase true & (n<=(0 - 1) | 2<=n | a<=0 & 1<=n | 2<=a & 1<=n) &
               MayLoop & {FLOW,(1,23)=__flow}
 */
relation A(int m, int n).
void delete(node x, int a)
  infer[n,a,A]
  requires x::ll<n> //& n > a & a > 0
  ensures x::ll<n - 1>& A(n,a);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else{
    delete(x.next, a-1);
  }
}

/* function to create a singly linked list with a nodes */
/*
node create_list_f(int a)
  requires true//a > 0
  ensures res::ll<a> & res!=null;
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
*/

//todo: bug
node create_list(int a)
  infer[a]
  requires true//a > 0
  ensures res::ll<a> & res!=null;
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
