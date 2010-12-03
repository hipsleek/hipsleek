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

void loop1(ref int i, int y) 
//  requires i>=0 & y<=0
//  ensures false;
//  requires i<0 
//  ensures i'=i; //'
 case {
  i<0 -> ensures "term": i'=i; //'
  i>=0 -> case {
  	y<=0 -> ensures "loop" : false; // loops
        y>0 -> ensures "term": true; // terminates
     } 
  }
{
  if (i>=0) { 
    i=i-y; 
    assert "term": (i+y)-(i'+y)>0;
    assert "term": i'+y>=0;
    loop1(i,y);
  }
}

int foo(int n) 
 case {
  n<0 -> ensures "nonterm" : false;
  // non-terminating inputs..
  n>=0 -> ensures "term" : res=2*n;
 }
// variance n
{ 
  if (n==0) return 0;
  else { 
        int m;
        m=n-1;
        assert n>m'; //'
        assert "term" : m'>=0;
        return 2+foo(m);
   }
}

int foo2(int n) 
case {
	n<0 -> requires [xx] xx=0 ensures false;
  	// non-terminating inputs..
  	n>=0 -> requires [xx] xx=1 ensures res= 2*n;
}
// variance n
{ 
  if (n==0) return 1;
  else { 
        int m;
        m=n-1;
        assert n>m'; //'
        assert m'>=0;
        assert xx!=1
                or
                m'>=0; //'  xx=1 -> m'>=0
        return 2+foo2(m);
       }
}

int foo3(int n) 
 case {
  n<0 -> ensures false;
  // non-terminating inputs..
  n>=0 -> ensures "term" : res=2*n;
 }
// variance n
{ 
  if (n==0) return 0;
  else {
		int m;
		m = n - 1;
		assert "term" : n>m;
		assert "term" : n>=0;
        return 2+foo3(m);
   }
}


int Ack(int m, int n)
case {
  m<0 -> ensures false;
  m=0 -> ensures res=n+1;
  m>0 -> case 
          { n<0 -> ensures false;
            n>=0 -> ensures res>0;
          }  
}
//requires n>=0 & m>=0
//ensures res>0;
// variance n,m
  { if (m==0) return n+1;
    else if (n==0) {
      int m1=m-1;
      //assert m1'>=0 & m'-m1'>0; //'
       return Ack(m1,1);
    }
  else {
    int m1=m-1;
    int n1=n-1;
    //assert m'=m' & n1'>=0 & n'-n1'>0; //'
    int r = Ack(m,n1);
    //assert m'-m1'>0 & m1'>=0; //'
    return Ack(m-1, r);
  }
}


/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<n1> * y::ll<n2> & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<m> & m=n1+n2;

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
		append(x.next, y);
      }
    }


node app2(node x, node y)
  requires x::ll<n> * y::ll<m> & n>=0
  ensures res::ll<n+m>;
 // variance n
{ 
  if (x==null) return y;
  else {
    node w=x.next;
    assert w'::ll<a> & n>a & a>=0; //'
    return new node(x.val,app2(w,y));
  } 
}

/* case {
   x>11 -> [] true ensures x'=10; \\'
   x<=11 -> [] true ensures x'=1; \\'
  }
*/

void loop(ref int x) 
 case {
   x>11 ->  requires true ensures  x'=10; //'
   x<=11 ->  requires true ensures x'=x-1; //'
  }
// variance x
{
  x=x-1;
  if (x>10) {
    assert x-x'>0; //' there is a decrease
    assert x'>=0; //' variance is bounded
    loop(x);
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




