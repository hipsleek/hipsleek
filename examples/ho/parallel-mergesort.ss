/*

   Description: Well-known parallel merge sort algorithm

*/

/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<xs:node,result:node>
inv result!=null;

pred_prim THRD2{(+)Q@Split}<xs:node,result:node>
inv result!=null;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<x,y> * self::dead<> -> %Q;

//this new thread multiplies x and y by 10
thrd create_thrd() // with %P
  requires true
  ensures (exists xs,result: res::THRD{xs::bnd<n, sm, bg> * result::node<_,null> & n > 0,
                                      result::node<_,ls> * ls::sll<n, smres, bgres> & smres >= sm & bgres <= bg}<xs,result>);

void fork_thrd(thrd t,node xs, node result)
  requires t::THRD{%P,%Q}<xs,result> * %P
  ensures  t::THRD2{%Q}<xs,result>;

void join_thrd(thrd t)
  requires exists xs, result: t::THRD2{%Q}<xs,result>
  ensures  t::dead<> * %Q;
/**************************************/


data node {
  int val; 
  node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or
  self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d <= bg 
  inv n >= 0; 

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
  self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs
  inv n >= 1 & sm <= lg & self!=null;

void destroy(node x)
  requires x::node<_,_>
  ensures emp;

/* function to count the number of elements of a list */
int count(node x)
  requires x::bnd<n, sm, bg> 
  ensures x::bnd<n, sm, bg> & res = n;
{
  int tmp;

  if (x == null)
    return 0;
  else
    return (1 + count(x.next));
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
node split_func(ref node x, int a)
  requires x::bnd<n, sm, bg> & a > 0 & n > a 
  ensures x'::bnd<n1, sm, bg> * res::bnd<n2, sm, bg> & n = n1 + n2 & n1 > 0 & n2 > 0 & n1 = a; //'

{
  node tmp;

  if (a == 1)
    {
      tmp = x.next; 
      x.next = null;
      return tmp;
    }
  else
    {
      a = a - 1;
      node tmp;
      bind x to (_, xnext) in {
        tmp = split_func(xnext, a);
      }
      return tmp;
    }
}

int div_2(int c) 
  requires true 
  ensures res + res = c;

node merge(node x1, node x2)
  requires x1::sll<n1, s1, b1> * x2::sll<n2, s2, b2>
  ensures res::sll<n1+n2, s3, b3> & s3 = min(s1, s2) & b3 = max(b1, b2);
{
  if (x2 == null)
    return x1; 
  else
    {
      if (x1 == null)
        return x2;
      else
        {
          x1 = insert(x1, x2.val);
          if (x2.next != null)
            {
              node tmp = merge(x1, x2.next);
              assert tmp'::sll<n1+n2,_,max(b1,b2)>  ; //'
                destroy(x2);
              return tmp;
            }
          else{
            destroy(x2);
            return x1;
          }
        }
    }
}

/* function to insert an element in a sorted list */
node insert(node x, int v)
  requires x::sll<n, xs, xl> & n > 0 
  ensures res::sll<n+1, sres, lres> & sres = min(v, xs) & lres =  max(v, xl);
{
  node tmp;

  if (v <= x.val)
    return new node(v, x);
  else
    {
      if (x.next != null)
        {
          x.next = insert(x.next, v);
          return x;
        }
      else
        {
          x.next = new node(v,null);
          return x;
        }
    }
}

// result is the head node pointing to the sorted list
void parallel_merge_sort(node xs,node result)
  requires xs::bnd<n, sm, bg> * result::node<_,null> & n > 0 
  ensures result::node<_,ls> * ls::sll<n, smres, bgres> & smres >= sm & bgres <= bg;
{
  if (xs.next != null)
    {
      int c, middle;
      node s1;
      node h1 = new node(0,null);
      node h2 = new node(0,null);
      c = count(xs);
      middle = div_2(c);
      s1 = split_func(xs, middle);
      // xs contains up to middle elements
      // s1 is the rest

      thrd id1 = create_thrd();
      thrd id2 = create_thrd();

      //h1 will be the head of the first sorted part
      fork_thrd(id1,s1,h1); 
      //h2 will be the head of the second sorted part
      fork_thrd(id2,xs,h2);

      join_thrd(id1);
      join_thrd(id2);

      //merge the two list together
      result.next = merge(h1.next,h2.next);
      destroy(h1); destroy(h2);
    }
  else {
    result.next = xs;
  }
}
