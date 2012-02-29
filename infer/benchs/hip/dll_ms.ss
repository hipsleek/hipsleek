/* doubly linked lists */

/* representation of a node */
data node {
  int val; 
  node prev;
  node next;	
}

/* view for a doubly linked list without size */
dll<p> == self = null
  or self::node<_ ,p , q> * q::dll<self> 
  inv true;


void dispose(ref node x)
  requires x::node<_,_,_>
  ensures x'=null;

relation A (node x).
void delete_list(ref node x)
  infer [A]
  requires x::dll<_>
  ensures A(x'); //x'=null
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

//true if the container size is 0, false otherwise.
relation EMPT1(bool a).
relation EMPT2(bool a).
bool empty(node x)
  infer[EMPT1,EMPT2]
  requires x::dll<_>
  case {
    x = null -> ensures EMPT1(res);//res
    x != null -> ensures EMPT2(res);//!(res)
  }
{
  if (x == null)
    return true;
  else
    return false;
}

//The number of elements that conform the list's content.
int size_helper(node x, ref int n)
  requires x::dll<_>
  ensures true;
{
  if (x==null) return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}

int size(node x)
  requires x::dll<_>
  ensures true;
{
  int n = 0;
  return size_helper(x, n);
}

// A reference to the first element in the list container.
int front(node x)
  infer [x]
  requires x::dll<_> // x!=null
  ensures true; // self_818::node<Anon_819,p_817,q_820>@M[Orig] * q_820::dll<self_818>@M[Orig]&Anon_19=p_817 & x=self_818 & res=Anon_819
{
  return x.val;
}

void swap(ref node x, ref node y)
  requires x::dll<_>*y::dll<_>
  ensures x'::dll<_>*y'::dll<_>;
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
void assign(ref node x, int n, int v)
  requires x::dll<_>
  ensures true;
{
  x = create_list(n, v);
}

void push_front(ref node x, int v)
  requires x::dll<_>
  ensures x'::node<v,_,q>*q::dll<_>;//'
{
  if (x==null) {
    node tmp = new node(v,null,x);
    x = tmp;
    //x = new node(v,null,null);
  }
  else {
    node tmp = new node(v,x.prev,x);
    x = tmp;
  }
}

//pop and return first element
node pop_front(ref node x)
  infer[x]
  requires x::dll<_>//x!=null
  ensures x'::dll<_>;//'
{
  node tmp = x;
  if (x.next == null)
    {
      x = x.next;
      tmp.next=null;
      return tmp;
    }
  else
    {
      x.next.prev = null;
      x = x.next;
      tmp.next = null;
      return tmp;
    }
}

/* append 2 doubly linked lists */
void append2(node x, node y)
  infer [x]
  requires x::dll<q> * y::dll<p> // x!=null
  ensures x::dll<q>;
{
	node tmp;
	if (x.next == null)
      {
		x.next = y;
		if (y != null)
          {
			y.prev = x;
          }
      }
	else
      {
		append2(x.next, y);
      }
}

/* return the first element of a doubly linked list */
node ret_first(node x)
  requires x::dll<_>
  ensures x::dll<_>;
{
  return x;
}

/* return the tail of a doubly linked list */
node get_next(node x)
  infer[x]
  requires x::dll<_> // x!=null
  ensures true; //  q_848::dll<self_846>@M[Orig] * self_846::node<Anon_847,prev_166_657',next_165_654'>@M[Orig]& x=self_846 & res=q_848 & prev_166_657'=null & next_165_654'=null
{
  node tmp = x.next;
  x.next = null;
  x.prev = null;
  return tmp;
}

/* function to set the tail of a list */
void set_next(node x, node y)
  infer[x]
  requires x::dll<_> * y::dll<_> // x!=null
  ensures x::dll<_>;
{
  if (y==null) 
    x.next = y;
  else
    {
      x.next = y;
      y.prev = x;
    }
}

void set_null2(node x)
  infer[x]
  requires x::dll<_> // x!=null
  ensures x::node<_,_,r>; //r=null
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(node x)
  infer[x]
  requires x::dll<_>  // x!=null
  ensures x::node<_,_,r>; // r=null
{
  x.next = null;
}

/* function to get the third element of a list */
// Fail
node get_next_next(node x)
  infer[x]
  requires x::dll<_> // x!=null
  ensures res::dll<_>;
{
  if (x.next!=null)
    return x.next.next;
  else 
    return null;
}

void insert(node x, int a)
  infer [x]
  requires x::dll<p> //&  x!=null  
  ensures x::dll<p>; 
{
  if (x.next == null)
    x.next = new node(a, x, null);
  else 
    insert(x.next, a);
}
/*
/* delete a node from a doubly linked list */
void delete(node x, int a)
  infer [x]
	requires x::dll<p> //& x!=null
	ensures x::dll<p>; 
{
	node tmp;
	node tmp_null = null;

	if (a == 1)
	{
      if (x.next.next != null)
		{
          x.next.next.prev = x;
          tmp = x.next.next;
          x.next = tmp;
		}
      else
        x.next = tmp_null;
	}
	else
      {
		delete(x.next, a-1);
      }
}
*/
/* function to delete the a-th node in a doubly linked list */
node delete2(ref node x, int a)
  requires x::dll<_>
  ensures res::dll<_>;
{
	if (x == null)
		return x;
	else 
  {
		if (x.val == a) 
    {
      if (x.next!=null)
        x.next.prev = null;
      return x.next;
    }
		else 
    {
      node nn = delete2(x.next, a);
      node nn2 = new node(x.val, null, nn);
      if (nn!=null)
        nn.prev = nn2;
      return nn2;
    }
	}
}


/* function to create a doubly linked list with a nodes */
node create_list(int n, int v)
  requires true 
  ensures res::dll<_>;
{
  node tmp;
  if (n == 0)
    {
      return null;
    }
  else
    {
      n = n - 1;
      tmp = create_list(n, v);
      node nn = new node (v, null, tmp);
      if (tmp==null)
        return nn;
      else
        {
          tmp.prev = nn;
          return nn;
        }
    }
}

/* function to reverse a doubly linked list */
relation REVERSE(node x).
void reverse(ref node xs, ref node ys)
  infer [REVERSE]
  requires xs::dll<p> * ys::dll<q>
  ensures ys'::dll<_> & REVERSE(xs'); // xs' = null
{
  if (xs != null)
    {
      node tmp;
      tmp = xs.next;
      xs.next = ys;
      if (ys!=null)
        ys.prev = xs;
      ys = xs;
      xs = tmp;
      reverse(xs, ys);
    }
}
/*
/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split1(ref node x, int a)
  infer[x]
  requires x::dll<p> & a > 0 //x!=null
  ensures x'::dll<p> * res::dll<_>;//'
{
	node tmp;
	if (a == 1)
	{
		tmp = x.next;
		x.next = null;
		return tmp;
	}
	else
	{
		a = a - 1;
		node tmp;
		bind x to (_, xprev, xnext) in
        {
			tmp = split1(xnext, a);
		}
		return tmp;
	}
}
*/
/*****************************************/
/*********SMALLFOOT EXAMPLES*************/
void list_traverse(node x)
  requires x::dll<p>
  ensures x::dll<p>;
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}

node list_copy(node x)
  requires x::dll<p>
  ensures x::dll<p> * res::dll<_>;
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    node nn = new node (x.val, null, tmp);
    if (tmp!=null)
      tmp.prev = nn;
    return nn;
  }
  else
    return null;
}

/*function to remove the first node which has value v in doubly linked list*/
void list_remove(node x, int v)
  infer[x]
  requires x::dll<p> // x!=null
  ensures x::dll<p>;
{
  if(x.next != null)
    {
    if(x.next.val == v)
      {
        node tmp = x.next;
        if (x.next.next!=null)
          x.next.next.prev = x;
        x.next = x.next.next;
        dispose(tmp);
      }
    else
      {
        list_remove(x.next, v);
      }
    }
}

/*function to remove the first node which has value v in nullable doubly linked list*/
node list_remove2(node x, int v)
  requires x::dll<p>
  ensures res::dll<p> ;
{
  node tmp;
  if(x != null)
    {
      if(x.val == v)
        {
          tmp = x;
          if (x.next!=null)
            x.next.prev = x.prev;
          x = x.next;
          dispose(tmp);
        }
      else
        {
          tmp = list_remove2(x.next, v);
          if (tmp!=null)
            tmp.prev = x;
          x.next = tmp;
        }
    }
  return x;
}

/*function to remove all nodes which have value v in nullable doubly linked list*/
node list_filter2(node x, int v)
  requires x::dll<p>
  ensures res::dll<_>;
{
  node tmp;
  if(x != null)
    {
      if(x.val == v)
        {
          tmp = x.next;
          dispose(x);
          x = tmp;
          x = list_filter2(x,v);
        }
      else
        {
          tmp = list_filter2(x.next, v);
          if (tmp!=null)
            tmp.prev = x;
          x.next = tmp;
        }
    }
  return x;
}

/**************************************************************/
/**********************SLAYER (SLL) EXAMPLES***************************/
/* function to return the first node being greater than v*/
node find_ge(node x, int v)
  requires x::dll<_>
  ensures res = null or res::node<m,_,_> & m > v;
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
void splice (ref node x, node y)
  requires x::dll<p> * y::dll<q>
  ensures x'::dll<_>;//'
{
  if(x == null)
    x = y;
  else
    {
      if(y != null)
        {
          node nx = x.next;
          node ny = y.next;
          x.next = y;
          if (y!=null)
            y.prev = x;
          splice(nx, ny);
          y.next = nx;
          if (nx!=null)
            nx.prev = y;
        }
    }
}

