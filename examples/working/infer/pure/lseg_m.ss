/* singly linked lists */

/* representation of a node */

data node {
	int val;
	node next;
}

/* view for a singly linked list */

ll1<> == self = null
	or self::node<_, q> * q::ll1<>
  inv true;

lseg<p> == self = p
	or self::node<_, q> * q::lseg<p>
  inv true;

void dispose(node x)
  requires x::node<_,_>
  ensures x=null;

void delete_list(ref node x)
   requires x::lseg<null>
  ensures x'=null;//'
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

/*ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

// Inferred Pure :[ x!=null, x!=null]
/* append two singly linked lists */
//relation APP (node p1, node p2).
void append(ref node x, node y)
  infer [x]
  requires x::lseg<null> * y::lseg<p1> //& x!=null
  ensures x::lseg<p2>;// & APP(p1,p2);
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* return the first element of a singly linked list */
relation RF (node p1, node p2).
node ret_first(node x)
  infer[RF]
  requires x::lseg<p1>
  ensures x::lseg<p2> & RF(p1,p2);//p1=p2
{
  return x;
}
//Inferred Pure :[ x!=null]
/* return the tail of a singly linked list */
relation GN (node p1).
node get_next(node x)
  infer[x,GN]
  requires x::lseg<null> //& x!=null
  ensures x::node<_,null> * res::lseg<p1> & GN(p1);//p1=null
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}
//Inferred Pure :[ x!=null]
/* function to set the tail of a list */
//relation SN (node p1, node p2).
 void set_next(ref node x, node y)
   infer[x]
   requires x::lseg<null> * y::lseg<p1> //& x!=null
   ensures x'::lseg<p1> ;//& SN(p1,p2);//'
{
	x.next = y;
}
//Inferred Pure :[ x!=null]
void set_null2(ref node x)
  infer[x]
  requires x::lseg<null> //& x!=null
  ensures x'::node<_,null>;//'
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

//Inferred Pure :[ x!=null]
/* function to set null the tail of a list */
void set_null(ref node x)
  infer[x]
  requires x::lseg<null>  //& x!=null
  ensures x'::node<_,null>;//'
{
  x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x)
  infer[x]
  requires x::lseg<null> //& x!=null
  ensures res::lseg<p2>;
{
  return x.next.next;
}

//Inferred Pure :[ x!=null, x!=null]
/* function to insert a node in a singly linked list */
void insert(ref node x, int a)
  infer[x]
  requires x::lseg<null> //&  x!=null
  ensures x'::lseg<p2>;//'
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

/* function to delete the a-th node in a singly linked list */
void delete(ref node x, int a)
//termination
  infer[x]
  requires x::lseg<null> //& n > a & a > 0
  ensures x'::lseg<p>;//'
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to create a singly linked list with a nodes */
node create_list(int a)
  requires true //a >= 0
  ensures res::lseg<null>;
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
//relation REV(node p1, node p2).
void reverse(ref node xs, ref node ys)
//infer  [REV]
  requires xs::lseg<null> * ys::lseg<p1>
  ensures ys'::lseg<p2> & xs' = null ;//& REV(p1,p2);
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
/*****************************************/
/*********SMALLROOT EXAMPLES*************/
//fail TRA
relation TRA(node p).
void list_traverse(node x)
  infer  [TRA]
  requires x::lseg<null>
  ensures x::lseg<p2> & TRA(p2);//p2=null
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}
//fail CPY
relation CPY(node p).
node list_copy(node x)
  infer[CPY]
  requires x::lseg<null>
  ensures x::lseg<null> * res::lseg<p> & CPY(p);//p=null
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

//Inferred Pure :[ x!=null, x!=null]
/*function to remove the first node which has value v in singly linked list*/
void list_remove(node x, int v)
  infer[x]
  requires x::lseg<null> //& x!=null // & x.val != v
  ensures x::lseg<p> ;//& m <= n;
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

/*function to remove the first node which has value v in nullable singly linked list*/
node list_remove2(node x, int v)
  requires x::lseg<null> //
  ensures res::lseg<null> ;//& m <= n;
{
  node tmp;
  if(x != null) {
    if(x.val == v) {
      tmp = x;
      x = x.next;
      dispose(tmp);
    }
    else {
      tmp = list_remove2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}

/*function to remove all nodes which have value v in nullable singly linked list*/
node list_filter2(node x, int v)
  requires x::lseg<null>
  ensures res::lseg<p>;// & m <= n;
{
  node tmp;
  if(x != null) {
    if(x.val == v){
      tmp = x.next;
      dispose(x);
      x = tmp;
      x = list_filter2(x,v);
    }
    else{
      tmp = list_filter2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}
/**************************************************************/
/**********************SLAYER (SLL) EXAMPLES***************************/
/* function to return the first node being greater than v*/
node find_ge(node x, int v)
  requires x::lseg<null>
  ensures res = null or res::node<m,_> & m > v;
{
  if(x == null)
    return null;
  else {
    if(x.val > v)
      return x;
    else
      return find_ge(x.next, v);
  }
}

/*function to splice 2 linked list*/
//fail at SP
relation SP(node p).
void splice (ref node x, node y)
  infer[SP]
  requires x::lseg<null> * y::lseg<null>
  ensures x'::lseg<p2> & SP(p2);//'p2=null
{
  if(x == null)
    x = y;
  else {
    if(y != null){
      node nx = x.next;
      node ny = y.next;
      x.next = y;
      splice(nx, ny);
      y.next = nx;
    }
  }
}
