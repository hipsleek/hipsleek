/* sorted lists with locking*/

/* representation of a node */
data node {
	int val; 
	node next;	
}

data lock{
  int locked; // 0 = unlocked, 1 = locked
}

global lock l;

void acquire() 
  requires l::lock<0> 
  ensures l'::lock<1> & l=l';
{
  l.locked = 1;
}

void release() 
  requires l::lock<1> 
  ensures l'::lock<0> & l=l';
{
  l.locked = 0;
}

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

