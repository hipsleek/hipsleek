/* parallel quick sort 
Sequential quicksort algorithm: a recursive procedure
- Select one of the numbers as pivot
- Divide the list into two sublists: a “low list” containing numbers
smaller than the pivot, and a “high list” containing numbers larger
than the pivot
- The low list and high list recursively repeat the procedure to sort
themselves
- The final sorted result is the concatenation of the sorted low list,
the pivot, and the sorted high list

IMPORTANT: Quicksort has some natural concurrency
The low list and high list can sort themselves concurrently

TO DO:

-  Multiple spec [Done]
-  Case analysis [Done]

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
  requires xs::bnd<n, sm, bg> & @full[xs] & @value[c] & sm <= c <= bg
    ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & @full[xs] & n = a+b;//'
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
  x = null -> requires y::sll<m,s2,b2> & @value[x,y]
             ensures res::sll<m,s2,b2>;
 x != null -> requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 & @value[x,y]
              ensures res::sll<nn+m, s0, b2>;
}
    /* requires y::sll<m,s2,b2> & x=null  */
    /* ensures res::sll<m,s2,b2>; */
	/* requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 */
	/* ensures res::sll<nn+m, s0, b2>; */

{
        node xn; 
        if (x==null) return y; /* segmentation bug when returning null */
        else {
         xn = append_bll(x.next,y);
         x.next = xn;
         return x;
        }
}

void seq_qsort(ref node xs)
 case{
  xs = null -> requires @full[xs]
               ensures @full[xs] & xs'=null;
  xs != null ->
     requires xs::bnd<n, sm, bg> & n>0 & @full[xs]
     ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg & @full[xs]; //'
}
    /* requires xs=null */
	/* ensures  xs'=null; */
	/* requires xs::bnd<n, sm, bg> & xs!=null & n>0 */
	/* ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg; //' */
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
        seq_qsort(tmp);
		tmp = new node(v, tmp);
        bind xs to (xsval, xsnext) in {
          seq_qsort(xsnext);
        }
        //dprint;
        xs = append_bll(xs.next, tmp);
	}
}

// parallel quick sort
// one thread
void para_qsort(ref node xs)
 case{
  xs = null -> requires @full[xs]
               ensures @full[xs] & xs'=null ;
  xs != null ->
     requires xs::bnd<n, sm, bg> & n>0 & @full[xs]
     ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg & @full[xs]; //'
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
        int id;
        id = fork(para_qsort,tmp);
        //dprint;
        bind xs to (xsval, xsnext) in {
          //dprint;
          para_qsort(xsnext);
        }
        //dprint;
        join(id);
		tmp = new node(v, tmp);
        //dprint;
        xs = append_bll(xs.next, tmp);
	}
}

// parallel quick sort
// two thread
void para_qsort2(ref node xs)
 case{
  xs = null -> requires @full[xs]
               ensures xs'=null & @full[xs];
  xs != null ->
     requires xs::bnd<n, sm, bg> & n>0 & @full[xs]
     ensures xs'::sll<n, smres, bgres> & smres >= sm & bgres < bg & @full[xs]; //'
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
        node tmp2 = xs.next;
        id2 = fork(para_qsort2,tmp2);
        /* seq_qsort(tmp2); */
        /* bind xs to (xsval, xsnext) in { */
        /* can not add fork here because it won't update xs.next */
        /*   id2 = fork(para_qsort2,xsnext); */
        /* } */
        //dprint;
        join(id1);
        join(id2);
        xs.next = tmp2;
		tmp = new node(v, tmp);
        xs = append_bll(xs.next, tmp);
	}
}
