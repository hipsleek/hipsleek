data cell {int val;}

data node {
  cell val;
  node next;
}

ll<n, v1, v2> == self = null & n = 0 
	or self::node<a, q>@v1 * a::cell<_>@v2 * q::ll<n-1, v1, v2>@v1 
  inv n >= 0;

ls<s,n, v1, v2> == self = null & n = 0 & s=0
	or self::node<a, q>@v1 * a::cell<v>@v2 * q::ls<s-v,n-1, v1, v2>@v1 
  inv n >= 0;

int length(node x)
  infer @pre [v1,v2]
  requires x::ll<n,v1,v2>@v1
  ensures x::ll<n,v1,v2>@v1 & res=n;
{
 
  if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}


int sum (node x)
  infer @pre [v1, v2]
  requires x::ll<n,v1,v2>@v1
  ensures  x::ll<n,v1,v2>;
{
 
 if (x==null) return 0;
 else {
      return x.val.val + sum(x.next);
 }
}

void update (node x)
  infer [v1, v2]
  requires x::ll<a,v1,v2>@v1
  ensures  x::ll<a,v1,v2>@v1;
{
 
 if (x==null) return;
 else {
//     cell y = x.val; // check why x.val.val = x.val.val+1 fails?
//     y.val = y.val + 1;
     x.val.val = x.val.val+1;
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
void delete(node x, int a)
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

