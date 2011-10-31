/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>
	inv n >= 0;

/* view for a sorted list */
/*sll<n, sm, lg> == self::node<sm, null> & n = 1 & sm = lg 
	or self::node<qmin, q> * q::sll<n-1, qs, ql> & q!=null & qmin <= qs 
	inv n >= 0 & sm <= lg;*/

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs
               inv n >= 1 & sm <= lg; 


node copy(node x) 
requires x::sll<n,sm,bg>@I & x!=null 
ensures res::sll<n,sm,bg>;
{
 node tmp1, tmp2;
 if (x.next==null) return new node(x.val, null);
    else {
	  tmp1 = copy(x.next);
	  tmp2 = new node(x.val, tmp1);
	      return tmp2;
	      }
}

/* function to insert an element in a sorted list */
node insert(node x, int v)
    requires x::sll<n, xs, xl>@I  & n > 0 
    ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres = max(v,xl);

{
        node tmp_null = null;
        node xn;
	node tmp;

   if (v <= x.val) {
		    //assume false;
		return new node(v, copy(x));
        }
	else {
       //assume false;
		if (x.next != null)
		{
	       
		        xn = insert(x.next, v);
			//x.next = xn;
			tmp = new node(x.val, xn);
			return tmp;
		}
		else
		{
		        xn = new node(v, tmp_null);
			tmp = new node(x.val, xn); 
			//x.next = new node(v, tmp_null);
			//return x;
			return tmp;
		}
    }
}


/* delete a node from a sorted list */
node delete(node x, int v)

	requires x::sll<n, xs, xl>@I
	ensures res::sll<nres, sres, lres> & sres >= xs & lres <= xl & n-1 <= nres <= n or res=null;
       // requires x::sll<n, v, v>@I
        //ensures res = null;

{
	node tmp; 

	//if (x != null)
		if (v < x.val)
			return copy(x);
		else
			if (v == x.val)
			  if (x.next == null)
			        return null;//copy(x);
			  else
				return copy(x.next);
			else
			
			 if(x.next != null) {
				//tmp = x.next;
				tmp = delete(x.next, v);
				return new node(x.val, tmp);
			}
			 else return copy(x);
	//else
		//return null;
}

/* get the tail of a sorted list */
node get_tail(node x)

	requires x::sll<n, xs, xl> & x != null
	ensures res::sll<n-1, sres, lres> & sres >= xs & lres <= xl; 

{
	return x.next;
}

/* transform a normal singly linked list in a sorted list */
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
