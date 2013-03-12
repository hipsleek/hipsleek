/* singly linked lists */

/* to complete */

/* representation of a node */
data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
  or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


relation A(int x, int y).
relation B(int x, int y, int z).

/*
Inferred Heap:[]
Inferred Pure:[ a>(0 - 1)]

FIXPOINT:  n>=2 & n=m+1

NEW RELS: [ ( exists(flted_12_569:n=2 & m=1 | -1+n=m & 1+flted_12_569=m & 2<=m)) -->  B(m,n), ( exists(a:exists(v_int_33_623:((2+v_int_33_623)<=n & m=1 & -1+
a=v_int_33_623 & m_622=0 & 1<=v_int_33_623 | -1+m=m_622 & 1<=m_622 & 1<=n | 
m=1 & m_622=0 & 1<=n | (2+v_int_33_623)<=n & -1+m=m_622 & -1+
a=v_int_33_623 & 1<=v_int_33_623 & 1<=m_622) & B(m_622,n_601) & 1+n_601=n))) -->  B(m,n)]

n>=0 & n>a 
 */

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
  infer [A,B]
  requires x::ll<n>  & x!=null & A(n,a)//& n > a & a > 0 
  ensures x::ll<m> & B(n,a,m);// n=m+1;
{
  if (a == 1)
  {
    //node tmp = x.next.next;
    //x.next = tmp;
    x.next = x.next.next;
    dprint;
  }
  else
  {
    delete(x.next, a-1);
    //dprint;
  }
}

