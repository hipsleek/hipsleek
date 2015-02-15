/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
                  self::node<d, p> * p::bnd<n1, sm, bg> & n= n1+1 & sm <= d < bg 
               inv n >= 0;

sll<n, sm, lg> == self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n1, qs, lg> & n= n1+1 & q != null & sm <= qs 
               inv n >= 1 & sm <= lg;

ll1<S> == self =  null & S={} 
	or self::node<v, r> * r::ll1<S1>  & S = union(S1, {v});

sll1<S> == self::node<v1, null> & S = {v1}
	or self::node<v2, r> * r::sll1<S1> & r != null 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x));

node partition(ref node xs, int c)
	requires xs::bnd<n, sm, bg> & sm <= c <= bg
        ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b;

{
	node tmp1;
	int v; 

	if (xs == null)
		return null;
	else
	{
		if (xs.val >= c)
		{
            v = xs.val;
			bind xs to (xsval, xsnext) in {
				tmp1 = partition(xsnext, c);
			}
			xs = xs.next;
			return new node(v, tmp1);
		}
		else {
			bind xs to (xsval, xsnext) in {
				tmp1 = partition(xsnext, c);
			}
			return tmp1;
		}
	}
}

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
node append_bll(node x, node y)
	requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2
	ensures res::sll<nn+m, s0, b2>;

{
        node xn; 

	if (x.next == null)
		x.next = y;
	else
         {
		xn = append_bll(x.next, y);
                x.next = xn;
         }

	return x; 
}

node append_bll1(node x, node y)
	requires x::sll1<S1> * y::sll1<S2> & 
	forall (a, b:(a notin S1 | b notin S2 | a <= b))
	ensures res::sll1<S3> & S3 = union(S1, S2);

{
        node xn; 

	if (x.next == null)
		x.next = y;
	else
         {
		xn = append_bll1(x.next, y);
                x.next = xn;
         }

	return x; 
}

void skip() requires true ensures true;

void qsort(ref node xs)
	requires xs::bnd<n, sm, bg> & n>0 
	ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg;//'
{
	node tmp;
        int v;
	bool b;

	if (xs == null)
		skip();
	else
	{
        v = xs.val;
		bind xs to (xsval, xsnext) in {
			tmp = partition(xsnext, v);
		}
        b = (xs.next == null);
		if (tmp == null)
			skip();
		else
			qsort(tmp);

		tmp = new node(v, tmp);
		if (b)
			xs = tmp;
		else
		{
            node xsnext = xs.next;
			qsort(xsnext);
            xs.next = xsnext;
			xs = append_bll(xs.next, tmp);
		}
	}	
}

void qsort1(ref node xs)
	requires xs::ll1<S> & S != {} 
	ensures xs'::sll1<S>; //'

{
	node tmp, tmp1;
        int v;
	bool b;

	if (xs == null)
		skip();
	else
	{
        dprint;
        v = xs.val;
		partition1(xs.next, tmp1, tmp, xs.val);
		xs.next = tmp1;
        b = (xs.next == null);
		if (tmp == null)
			skip();
		else
			qsort1(tmp);

		tmp = new node(v, tmp);
		if (b)
			xs = tmp;
		else
		{
        	bind xs to (xsval, xsnext) in {
				qsort1(xsnext);
			}
			xs = append_bll1(xs.next, tmp);
		}
	}	
}







                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            
