data cell {int val;}

data node {
  int val;
  node next;
}

ll0<n,v1> == self = null & n = 0 
	or self::node<v1, q> * q::ll0<n-1,v1> 
  inv n >= 0;

ll<n,v1,v2> == self = null & n = 0 
	or self::node<a@v1, q@v2> * q::ll<n-1,v1,v2> 
  inv n >= 0;

ll1<n,v1> == self = null & n = 0 
  or self::node<a@v1, q> * q::ll1<n-1,v1> 
  inv n >= 0;

ll2<n,v1> == self = null & n = 0 
  or self::node<a, q@v1> * q::ll2<n-1,v1> 
  inv n >= 0;

/*
int length(node x)
  requires x::ll<n,@A,@L>
  ensures  x::ll<n,@A,@L> & res=n; //bug - success with @M
{
 if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}
*/
/*
int sum_node (node x, node y)
  requires x::node<a@L,b@A> * y::node<c@L,d@A>
  ensures res = a + c;
{
 return x.val + y.val;
}
*/
/*
int sum (node x)
  requires x::ll<n,@L,@L>
  ensures  x::ll<n,@L,@L>;
{
 
 if (x==null) return 0;
 else {
      return x.val + sum(x.next);
 }
}
*/

void update0 (node x)
  requires x::ll<n,@M,@I>
  ensures  x::ll<n,@M,@M>;
{
 return;
}

void update1 (node x)
  requires x::ll<n,@M,@I>
  ensures  x::ll<n,@M,@M>;
{
 if (x==null) return;
 else {
   return;
 }
 // return;
}

void update (node x)
  requires x::ll<n,@M,@I>
  ensures  x::ll<n,@M,@M>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update(y);
     }
     }

// fail - ok
void update11 (node x)
  requires x::ll1<n,@I>
  ensures  x::ll1<n,@I>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update11(y);
     }
}

//success - ok
void update12 (node x)
  requires x::ll1<n,@M>
  ensures  x::ll1<n,@M>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update12(y);
     }
}

// fail - ok
void update13 (node x)
  requires x::ll1<n,@I>
  ensures  x::ll1<n,@M>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update13(y);
     }
}

// success - ok
void update14 (node x)
  requires x::ll1<n,@M>
  ensures  x::ll1<n,@I>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update14(y);
     }
}


// fail - ok
void update21 (node x)
  requires x::ll2<n,@A>
  ensures  x::ll2<n,@A>;
{
 
 if (x==null) return;
 else {
    x.val = x.val + 1;
     node y = x.next;
     dprint;
     update21(y);
     }
}

//success - BUG!!
void update22 (node x)
  requires x::ll2<n,@I> //@I
  ensures  x::ll2<n,@M>;//@I
{
  if (x==null) return;
  else {
    //x.val = x.val + 1;
    //int z = x.val;
    //node y = x.next;
    dprint;
    //update22(y);
    update22(x.next);
  }
}

// fail - ok
void update23 (node x)
  requires x::ll2<n,@I>
  ensures  x::ll2<n,@M>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update23(y);
     }
}

//fail - ok 
void update24 (node x)
  requires x::ll2<n,@M>
  ensures  x::ll2<n,@I>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     node y = x.next;
     update24(y);
     }
}

void update2 (node x)
  requires x::ll0<n,8>
  ensures  x::ll0<n,8>;
{
 
 if (x==null) return;
 else {
   //x.val = x.val + 1;
     update2(x.next);
 }
}

void delete (ref node x)
  requires x::ll<a,@L,@L>
  ensures  true;
{

 if (x == null) return;
 else {
       if (x.val == 0 ) {
          x = x.next;
	  delete (x);
       } else {
	       delete (x.next);
       }
 }
}


/* function to delete the a-th node in a singly linked list */
/*
void delete(node x, int a)
  requires x::ll<n,@L,@M> & n > a & a > 0 
  ensures x::ll<n - 1,@L,@M>;
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

*/
