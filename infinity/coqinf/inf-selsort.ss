/* selection sort with infinity*/

data node {
	int val; 
	node next; 
}

bnd1<n,mi,mx> == self = null & n = 0 & mi = \inf & mx=~\inf or 
  self::node<d, p> * p::bnd1<n-1, tmi,tmx> & mi = min(d, tmi) & mx=max(d,tmx) & ~\inf<d<\inf 
  inv self=null & n=0 & mi=\inf & mx=~\inf |
      self!=null & n=1 & mi=mx & ~\inf<mi<\inf |
      self!=null & n>1 & mi<=mx & ~\inf<mi & mx<\inf;

sll<n, mi,mx> == 
   self = null & mi = \inf & mx = ~\inf & n = 0
 or self::node<mi, null> & n=1 & ~\inf<mi<\inf & mi=mx
 or self::node<mi, q> * q::sll<n-1, qs,mx> & ~\inf<mi<\inf & mi <= qs
      &  q!=null 
  inv self=null & n=0 & mi=\inf & mx=~\inf |
      self!=null & n>0 & mi<=mx  & ~\inf<mi & mx<\inf
;


int find_min(node x)
     requires x::bnd1<n, mi,mx> & n > 0
     ensures x::bnd1<n, mi,mx> & res = mi & ~\inf<res<\inf;
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else
	{	
		tmp = find_min(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}

void delete_min(ref node x, int a)
  requires x::bnd1<n, mi,mx> & n >= 1 & a = mi
  case {
    n=1 -> ensures x'=null;
    n!=1 -> ensures x'::bnd1<n-1,mi1,mx> & mi<=mi1;
    }  
{
	if (x.val == a)
		x = x.next;
	else {
        //assume false;
		bind x to (_, xnext) in {
                   //assume xnext'=null or xnext'!=null;
			delete_min(xnext, a);
		}
	}
}

/*
node selection_sort(node x)

 requires x::bnd1<n,mi,mx>
 ensures res::sll<n,mi,mx> ;

{
	int minimum;
	node tmp, tmp_null = null;
	if (x == null) return null;
	else
	{
	    minimum = find_min(x);
	    delete_min(x, minimum);
        if (x==null) return new node(minimum, tmp_null);
        else {
		  tmp = selection_sort(x);
		  return new node(minimum, tmp);
        }
	}
}
*/
