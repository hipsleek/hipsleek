/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
                  self::node<d, p> * p::bnd<n1, sm, bg> & n= n1+1 & sm <= d < bg 
               inv n >= 0;

/*
bnd2<n,S> == self=null & n=0 & S={}
      or self::node<v,q> * q::bnd2<n1,S1> & n1+1=n & S=union({v},S1) 
      inv n>=0;
 
sll2<n,S> == self=null & n=0 & S={}
      or self::node<v,q> * q::sll2<n1,S1> & n1+1=n & S=union({v},S1) & forall (x : (x notin S1 | v<=x))
      inv n>=0;
*/

sll<n, sm, lg> == self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n1, qs, lg> & n= n1+1 & q != null & sm <= qs 
               inv n >= 1 & sm <= lg;

node partition(ref node xs, int c)
	requires xs::bnd<n, sm, bg> & sm <= c <= bg
        ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b;
/*
        requires xs::bnd2<n,S>
        ensures xs'::bnd2<a,S1> * res::bnd2<b,S2> & S=union(S1,S2) & n=a+b
	   & forall(x : (x notin S1 | x<c)) 
	   & forall(y : (y notin S2 | y>=c)) ;
*/
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

/* function to append 2 bounded lists */
node append_bll(node x, node y)
        requires y::sll<m,s2,b2> & x=null 
        ensures res::sll<m,s2,b2>;
	requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2
	ensures res::sll<nn+m, s0, b2>;
/*
	requires x::sll2<n,S1> * y::sll2<m,S2> 
           & forall(u : (u notin S1 | forall( v : (v notin S2 | u<=v))))
        ensures  res::sll2<n+m,union(S1,S2)>;
*/

{
        node xn; 

        if (x==null) return y;
        else {
         xn = append_bll(x.next,y);
         x.next = xn;
         return x;
    /*
	 if (x.next == null)
		x.next = y;
	 else
          {
	 	xn = append_bll(x.next, y);
                x.next = xn;
          }
	 return x; 
     */
        }
}


void qsort(ref node xs)
    requires xs=null
	ensures  xs'=null;
	requires xs::bnd<n, sm, bg> & n>0 
	ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg;
/*
	requires xs::bnd2<n,S> & n>0 
	ensures xs'::sll2<n,S>; 
*/
{
	node tmp;
        int v;
	bool b;

	if (xs != null)
	{
        v = xs.val;
		bind xs to (xsval, xsnext) in {
			tmp = partition(xsnext, v);
		}
        b = (xs.next == null);
		if (tmp != null)
			qsort(tmp);

		tmp = new node(v, tmp);
		if (b)
			xs = tmp;
		else
		{
			bind xs to (xsval, xsnext) in {
				qsort(xsnext);
			}
			//dprint;
			xs = append_bll(xs.next, tmp);
		}
	}	
}

