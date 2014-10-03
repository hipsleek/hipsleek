/*

  Description: well-known parallel quick sort algorithm

*/

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
      self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d < bg 
      inv n >= 0;

sll<n, sm, lg> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 
  or self::node<sm, q> * q::sll<n-1, qs, lg> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;

//parition a list into 2 sublists.
// xs constains elements < c
// res include elemts >= c
node partition(ref node xs, int c)
  requires xs::bnd<n, sm, bg> & sm <= c <= bg //& @full[xs] & @value[c]
    ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b; // & @full[xs];//'
{
	node tmp1;
	int v; 

	if (xs == null)
		return null;
	else
	{
		if (xs.val >= c)
		{
          /* assume false; */
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
 case{
  x = null -> requires y::sll<m,s2,b2> //& @value[x,y]
             ensures res::sll<m,s2,b2>;
  x != null -> requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 //& @value[x,y]
              ensures res::sll<nn+m, s0, b2>;
}
{
        node xn; 
        if (x==null) return y; /* segmentation bug when returning null */
        else {
         xn = append_bll(x.next,y);
         x.next = xn;
         return x;
        }
}

// parallel quick sort
// two thread
void para_qsort2(ref node xs)
 case{
  xs = null -> requires true //@full[xs]
               ensures xs'=null; // & @full[xs];
  xs != null ->
     requires xs::bnd<n, sm, bg> & n>0 // & @full[xs]
     ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg; // & @full[xs]; //'
}
{
	node tmp;
    int v;

	if (xs != null)
	{
        v = xs.val;
		bind xs to (xsval, xsnext) in {
			tmp = partition(xsnext, v);
		}

        int id1,id2;
        id1 = fork(para_qsort2,tmp);

        node tmp2;
        tmp2 = xs.next;
        id2 = fork(para_qsort2,tmp2);
        join(id1);
        join(id2);
        xs.next = tmp2;
		tmp = new node(v, tmp);
        xs = append_bll(xs.next, tmp);
	}
}
