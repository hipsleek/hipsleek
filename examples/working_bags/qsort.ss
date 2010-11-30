/* quick sort */

data node {
	int val; 
	node next; 
}

ll1<S> == self =  null & S={} 
	or self::node<v, r> * r::ll1<S1>  & S = union(S1, {v});

sll1<S> == self::node<v1, null> & S = {v1}
	or self::node<v2, r> * r::sll1<S1> & r != null 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x))
  inv self !=null;

void partition1(node x, ref node y, ref node z, int c)
	requires x::ll1<S> 
        ensures y'::ll1<S1> * z'::ll1<S2> & S = union(S1, S2) &
	forall(a: (a notin S1 | a <= c)) 
	& forall(b: (b notin S2 | b > c));
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

	/*if (xs == null)
		return null;
	else
	{
		if (xs.val >= c)
		{
            v = xs.val;
			bind xs to (xsval, xsnext) in {
				tmp1 = partition1(xsnext, c);
		}
			xs = xs.next;
			return new node(v, tmp1);
		}
		else {
			bind xs to (xsval, xsnext) in {
				tmp1 = partition1(xsnext, c);
			}
			return tmp1;
		}
	}*/
}

/* function to append 2 bounded lists */
node append_bll1(node x, node y)
	requires x::sll1<S1> * y::sll1<S2> & 
	forall (a, b:(a notin S1 | b notin S2 | a <= b | a>0 & a<=0))
	ensures res::sll1<S3> & S3 = union(S1, S2);

{
  node xn; 
	if (x.next == null)
    {x.next = y;
    }
	else
    {
		xn = append_bll1(x.next, y);
                x.next = xn;
    }

	return x; 
}

void skip() requires true ensures true;

void qsort1(ref node xs)
	requires xs::ll1<S> & S != {} 
	ensures xs'::sll1<S>;

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
			xs = append_bll1(xs.next, tmp);
     // assume false;
		}
	}
  //assume false;	
}







                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            
