/*

  Description: well-known parallel quick sort algorithm

*/

/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<h:node>
inv h!=null;

pred_prim THRD2{(+)Q@Split}<h:node>
inv h!=null;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<h> * self::dead<> -> %Q;

//this new thread multiplies x and y by 10
thrd create_thrd() // with %P
  requires true
  ensures (exists h: res::THRD{ h::node<_,xs> * xs::bnd<n, sm, bg> & n>=0,
                                h::node<_,xs1> & xs1=null & n=0
                                or h::node<_,xs2> * xs2::sll<n, smres, bgres> & smres >= sm & bgres < bg & n>0
                               }<h>);

void fork_thrd(thrd t,node h)
  requires t::THRD{%P,%Q}<h> * %P
  ensures  t::THRD2{%Q}<h>;

void join_thrd(thrd t)
  requires exists h: t::THRD2{%Q}<h>
  ensures  t::dead<> * %Q;
/**************************************/

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

void destroy(node x)
  requires x::node<_,_>
  ensures emp;

//parition a list into 2 sublists.
// xs constains elements < c
// res include elemts >= c
node partition(ref node xs, int c)
  requires xs::bnd<n, sm, bg> & sm <= c <= bg 
  ensures xs'::bnd<a, sm, c> * res::bnd<b, c, bg> & n = a+b; //'
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
          node tmp = xs;
          xs = xs.next;
          destroy(tmp);
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
  x = null -> requires y::sll<m,s2,b2> 
    ensures res::sll<m,s2,b2>;
  x != null -> requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2
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
// two threads
void para_qsort(node h)
  requires h::node<_,xs> * xs::bnd<n, sm, bg> & n>=0
  ensures h::node<_,xs1> & xs1=null & n=0
          or h::node<_,xs2> * xs2::sll<n, smres, bgres> & smres >= sm & bgres < bg & n>0;
{
  node xs = h.next;
  if (xs != null)
    {
      node tmp;
      int v;
      v = xs.val;
      bind xs to (xsval, xsnext) in {
        tmp = partition(xsnext, v);
      }

      thrd id1 = create_thrd();
      thrd id2 = create_thrd();

      node h1 = new node(0,tmp);
      fork_thrd(id1,h1);

      node h2 = new node(0,xs.next);
      fork_thrd(id2,h2);

      join_thrd(id1);
      join_thrd(id2);

      xs.next = h2.next;
      node tmp1 = new node(v, h1.next);
      node tmp2 = xs;
      xs = append_bll(xs.next, tmp1);
      destroy(tmp2);
      destroy(h1);
      destroy(h2);
    }
  h.next = xs;
}


