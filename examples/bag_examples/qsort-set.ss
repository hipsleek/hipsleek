/* quick sort */

data node {
	int val; 
	node next; 
}

ll<S> == self=null & S={} 
     or self::node<v, r> * r::ll<S1>  & S = union(S1, {v});

sorted<S> == self=null & S = {}
  or self::node<v2, r> * r::sorted<S1> 
  & S = union(S1, {v2}) & forall(x: (x notin S1 | v2 <= x))
;

void partition1(node x, ref node y, ref node z, int c)
	requires x::ll<S> 
        ensures y'::ll<S1> * z'::ll<S2> & S = union(S1, S2) &
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

}

node append_bll(node x, node y)
  requires x::sorted<S1> * y::sorted<S2> & S1!={} &
	forall (a, b:(a notin S1 | b notin S2 | a <= b))
	ensures res::sorted<S3> & S3 = union(S1, S2);
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

void skip() requires true ensures true;

void qsort1(ref node xs)
 case {
   xs=null -> ensures xs'::sorted<S> & S={};
  xs!=null ->  requires xs::ll<S> & S!={}
               ensures xs'::sorted<S>; //'
 }
{
	node tmp, tmp1;
        int v;
	bool b;
	if (xs == null)
		skip();
	else
	{
           v = xs.val;
		partition1(xs.next, tmp1, tmp, xs.val);
		xs.next = tmp1;
                b = (xs.next == null);
                qsort1(tmp);
		tmp = new node(v, tmp);
		if (b)
			xs = tmp;
		else
		{
        	bind xs to (xsval, xsn) in {
				qsort1(xsn);
			}
			xs = append_bll(xs.next, tmp);
                }
	}	
}
