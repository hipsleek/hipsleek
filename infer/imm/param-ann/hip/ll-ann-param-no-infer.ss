data cell {int val;}

data node {
  int val;
  node next;
}


ll<n,v1,v2> == self = null & n = 0 
	or self::node<a@v1, q@v2> * q::ll<n-1,v1,v2> 
  inv n >= 0;

int length(node x)
  requires x::ll<n,@A,@L>
  ensures  x::ll<n,@A,@L> & res=n;
{
 if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}

int sum_node (node x, node y)
  requires x::node<a@L,b@A> * y::node<c@L,d@A>
  ensures res = a + c;
{
 return x.val + y.val;
}

int sum (node x)
  requires x::ll<n,@L,@L>
  ensures  x::ll<n,@L,@A>;
{
 
 if (x==null) return 0;
 else {
      return x.val + sum(x.next);
 }
}


void update (node x)
  requires x::ll<a,@M,@A>
  ensures  x::ll<a,@M,@A>;
{
 
 if (x==null) return;
 else {
     x.val = x.val + 1;
     update(x.next);
 }
}


/*void delete (ref node x)
  infer [v1, v2]
//  requires x::ll<a,v1,v2>@v1
  requires x::ll<a,v1,v2>@L & v1<:@L & v2<:@L
  ensures  true;
{

 if (x == null) return;
 else {
       if (x.val.val == 0 ) {
          x = x.next;
	  delete (x);
       } else {
	       delete (x.next);
       }
 }
}*/


/* function to delete the a-th node in a singly linked list */
/*void delete(node x, int a)
infer  @pre [v1, v2]
requires x::ll<n,v1,v2>@v1 & n > a & a > 0 
//requires x::ll<n,v1,v2>@M & v1<:@M & v2<:@M & n > a & a > 0 
ensures x::ll<n - 1,v1,v2>@M & v1<:@M & v2<:@M;
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
