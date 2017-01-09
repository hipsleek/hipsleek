/* sorted lists with coarse-grained locking*/

/* representation of a node */
data node {
	int val; 
	node next;	
}

data lock{
  int locked; // 0 = unlocked, 1 = locked
}

global lock l;

void acquire() requires l::lock<0>  ensures l::lock<1>;
void release() requires l::lock<1> ensures l::lock<0>;

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>
	inv n >= 0;

/* view for a sorted list */
sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
	or (exists qs,ql: self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;



/* insert an element in a sorted list
- recursive 
- coarse-grained

- Remarks:
Not efficient, acquire and release many times. Try/catch/finally might help.
*/
/*
node insert(node x, int v)

  requires x::sll<n, sm, lg>
  ensures res::sll<n + 1, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 

{
	node tmp;

    acquire(l);
	if (x == null){
      release(l);
	  return new node(v, null);
    }
	else
	{
      if (v <= x.val){
        release(l);
		return new node(v, x);
      }
	  else
      {
        tmp = x.next;
		x.next = insert(tmp, v);
        release(l);
		return x;
	  }
	}
}
*/

/* insert an element in a sorted list 
- while loop 
*/
// x is the head

/*
node insert_loop(node x, int v)

//  requires x::sll<n, sm, lg>
//  ensures res::sll<n + 1, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 
  requires l::lock<0>
  ensures true;
  

{
  node pred;
  node curr;
  node tmp;
  /*
  //lock l;

  acquire();
  assume false;

    if (x == null){
      release();
	  return new node(v, null);
    }else{
		if (v <= x.val){
          release();
		  return new node(v, x);
        }
		else
		{
          pred=x;
          curr=x.next;
          while (v > curr.val && curr != null){
              pred = curr;
              curr = curr.next;
          }
          tmp = new node(v,curr);
          pred.next=tmp;
          release();
          return x;
		}
	}
}

*/
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
