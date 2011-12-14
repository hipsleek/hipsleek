/* LOC: 86 */
/* quick sort */

data node {
	int val; 
	node next; 
}

ll<n> == self =  null & n = 0
	or self::node<v, r> * r::ll<n1> & n = 1 + n1 
	inv n >= 0;

sll<n> == self::node<v1, null> & n = 1 
	or self::node<v2, r> * r::sll<n1> & r != null & n = n1 + 1
  inv n >= 1 & self !=null;

void partition1(node x, ref node y, ref node z, int c)
	requires x::ll<n> 
    ensures y'::ll<n1> * z'::ll<n2> & n = n1 + n2;
{
	node tmp1;
	int v; 

	if (x==null) {
		y = null;
		z = null;
		return;
	}
	else {
		partition1(x.next, y, z, c);
		if (x.val <= c)	y = new node(x.val, y);
		else z = new node(x.val, z);
		return;
	}
}

/* function to append 2 bounded lists */
node append_bll(node x, node y)
	requires x::sll<n1> * y::sll<n2>	
	ensures res::sll<n3> & n3 = n1 + n2;

{
  node xn; 
	if (x.next == null)
    {
		x.next = y;
    }
	else
    {
		xn = append_bll(x.next, y);
        x.next = xn;
    }

	return x; 
}

void skip() requires true ensures true;

void qsort1(ref node xs)
	requires xs::ll<n> & n > 0
	ensures xs'::sll<n>;

{
	node tmp, tmp1;
	int v;
	bool b;
	if (xs != null) 
	{
    v = xs.val;
    bind xs to (xsval, xsnext) in 
    {
      partition1(xsnext, tmp1, tmp, xsval);
      xsnext = tmp1;			
    }
    b = (xs.next == null);
		if (tmp != null) qsort1(tmp);
		tmp = new node(v, tmp);
		if (b) xs = tmp;
		else
		{
			bind xs to (xsval, xsnext) in {
				qsort1(xsnext);
			}
			xs = append_bll(xs.next, tmp);
		}
	}
}







                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            
