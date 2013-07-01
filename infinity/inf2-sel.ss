/* selection sort */

data node {
	int val; 
	node next; 
}

/* fail to prove for delete_min
bnd1<n,mi,mx> == 
  self = null & n = 0 & mi = \inf & mx=-\inf or 
  self::node<d, p> * p::bnd1<n-1,tmi,tmx> & mi=min(d,tmi) 
  & mx=max(d,tmx) & -\inf<d<\inf 
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n=1 & mi=mx & -\inf<mi<\inf |
      self!=null & n>1 & mi<=mx & -\inf<mi & mx<\inf
  ;
*/

// 3 cases needed to prove delete_min
bnd1<n,mi,mx> == self = null & n = 0 & mi = \inf & mx=-\inf or 
  self::node<d, p> * p::bnd1<n-1, tmi,tmx> & mi = min(d, tmi) & mx=max(d,tmx) & -\inf<d<\inf 
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n=1 & mi=mx & -\inf<mi<\inf |
      self!=null & n>1 & mi<=mx & -\inf<mi & mx<\inf;

/*
sll<n, sm,mx> == self = null & sm = \inf & mx = -\inf & n = 0
 or self::node<sm, q> & q=null & sm = mx & -\inf<sm<\inf
 or self::node<sm, q> * q::sll<n-1, qs,mx> & sm <= qs & q!=null 
     & -\inf<sm & mx<\inf
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n=1 & mi=mx & -\inf<mi<\inf  |
      self!=null & n>1 & mi<=mx  & -\inf<mi & mx<\inf;
*/
//   inv n >= 0;

sll<n, mi,mx> == 
   self = null & mi = \inf & mx = -\inf & n = 0
 or self::node<mi, null> & n=1 & -\inf<mi<\inf & mi=mx
 or self::node<mi, q> * q::sll<n-1, qs,mx> & -\inf<mi<\inf & mi <= qs
      &  q!=null //& -\inf<mx<\inf //& n>1
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n>0 & mi<=mx  & -\inf<mi & mx<\inf
;


int find_min(node x)
     requires x::bnd1<n, mi,mx> & n > 0
     ensures x::bnd1<n, mi,mx> & res = mi & -inf<res<\inf;
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
     //& mi<=mi1  
     //& (n>1 & mx1=mx & mi<=mi1 | n=1 & mx1=(-\inf) & mi1=\inf);
/*
  requires x::bnd1<n, mi,mx> & n >= 1 & a = mi
  case {
    n=1 -> ensures x'=null ;
   n!=1 -> ensures x'::bnd1<n-1, mi1,mx> & x'!=null & mi1 >= mi;//'
  }
*/
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

node selection_sort(ref node x)
/*
	requires x::bnd1<n, mi,mx> & n>0
	ensures res::sll<n, mi,mx> & x' = null;//'
    VERY slow for bytecode
*/
 requires x::bnd1<n, mi,mx> & n > 0 
 case {
    n=1 -> ensures res::sll<n, mi,mx> & mi=mx & x' = null;//'
    n!=1 -> ensures res::sll<n, mi,mx> & x' = null;//'
 }
{
	int minimum;
	node tmp, tmp_null = null;	

	minimum = find_min(x);
	delete_min(x, minimum);

	if (x == null)
		return new node(minimum, tmp_null);
	else
	{
		tmp = selection_sort(x);
        //assert false;
		return new node(minimum, tmp);
	}
}













