/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;
    lock l;
}

data lock{
  int locked; // 0 = unlocked, 1 = locked
}

void acquire(lock l) requires true ensures true;
void release(lock l) requires true ensures true;

/* view for a singly linked list */
ll<n> == self = null & n = 0 
  or self::node<_, q, _> * q::ll<n-1>
	inv n >= 0;

/* view for a sorted list */
sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
  or (exists qs,ql: self::node<qmin, q, _> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;

/* insert an element in a sorted list - recursive */
/*
node insert(node x, int v)

	requires x::sll<n, sm, lg>
	ensures res::sll<n + 1, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 

{
	node tmp;

	if (x == null)
		return new node(v, null);
	else
	{
		if (v <= x.val)
			return new node(v, x);
		else
		{
			tmp = x.next;
			x.next = insert(tmp, v);
			return x;
		}
	}
}
*/

/* insert an element in a sorted list - while loop */
// x is the head
node insert_loop(node x, int v)

//  requires x::sll<n, sm, lg>
//  ensures res::sll<n + 1, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 

{
  node pred;
  node curr;
  node tmp;
  lock l = new lock(0);

  //??? how to acquire when x = null or one-element list?
  //??? a list with 2 dummy nodes (head/tail) can solve this?
  if (x == null)
    return new node(v, null, l);
  else
	{
      if (v <= x.val)
        return new node(v, x, l);
      else
		{
          pred=x;
          acquire(pred.l);
          curr=x.next;
          acquire(curr.l);
          while (v > curr.val && curr != null){
            release(pred.l);
            pred = curr;
            curr = curr.next;
            acquire(curr.l);
          }
          tmp = new node(v,curr, l);
          pred.next=tmp;
          release(curr.l);
          rekease(pred.l);
          return x;
		}
	}
}


 /* delete a node from a sorted list */
/*
node delete(node x, int v)

  requires x::sll<n, xs, xl>
  ensures res::sll<nres, sres, lres> & sres >= xs & lres <= xl & n-1 <= nres <= n;

{
	node tmp; 

	if (x != null)
		if (v < x.val)
			return x;
		else
			if (v == x.val)
				return x.next;
			else
			{
				tmp = x.next;
				x.next = delete(tmp, v);
				return x;
			}
	else
		return null;
}
*/

/* delete a node from a sorted list */
/*
node delete_loop(node x, int v)

	requires x::sll<n, xs, xl>
	ensures res::sll<nres, sres, lres> & sres >= xs & lres <= xl & n-1 <= nres <= n;

{
  node pred;
  node curr;
  if (x != null){
    if (v < x.val){
      return x;
    }else{
      pred=x;
      curr=x.next;
      while (v > curr.val && curr != null){
        pred = curr;
        curr = curr.next;
      }
      if (v == curr.val){
        pred.next=curr.next;
      }else{
        // v < curr.val -> nothing to delete
      }
      return x;
    }
  }else{
    return null;
  }
}
*/


/*
node insert2(node x, node vn)
	requires x::sll<n, sm, lg> *  vn::node<v, _>
	ensures res::sll<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		vn.next = null;
		return vn;
	}
	else if (vn.val <= x.val) {
		vn.next = x;
		return vn;
	}
	else {
		x.next = insert2(x.next, vn);
		return x;
	}
}

*/

/* get the tail of a sorted list */
/*
node get_tail(node x)

	requires x::sll<n, xs, xl> & x != null
	ensures res::sll<n-1, sres, lres> & sres >= xs & lres <= xl; 

{
	return x.next;
}
*/

/* transform a normal singly linked list in a sorted list */
/*
void insertion_sort(node x, ref node y)

	requires x::ll<n> * y::sll<m1, ys1, yl1>
	ensures y'::sll<n + m1, _, _> * x::ll<n>;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}

void id(int x)
	requires true ensures true;
{
	int n = 1; 

	n ++;
	id(n);
}

*/
