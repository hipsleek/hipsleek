/** node to build a linked list */
data node{
   int val;
   node next;
}

/** node to build a linked list of linked lists */
data nodell{
   node   val;
   nodell next;
}

relation R(int n, int m, int z).
relation R1(int n, int m, int z) == n = m + z.
relation R2(int n, int m, int z) == n = 1 + m + z.

/** a simple linked list */
pred list<n> ==  self = null & n = 0  or
    self::node<_,q> * q::list<n-1>
    inv n>=0;

/** a list of simple linked lists. */
pred llist<n,m> ==  self = null & n = 0  or
    self::nodell<lst,q> * lst::list<nn> * q::llist<n-1,mm> & m = nn + mm
    inv n>=0;

/** a list of simple linked lists. */
pred llistR<n,m,R> ==  self = null & n = 0  & m = 0 or
    self::nodell<lst,q> * lst::list<nn> * q::llistR<n-1,mm,R> & R(m,nn,mm)
    inv n>=0.

/* returns the size of the linked list pointed by x */
int length_list(node x)
    requires x::list<n>@L
    ensures  res = n;
{
 if (x==null) return 0;
 else return 1 + length_list(x.next);
}


/* returns the sum of the sizes of all lists reachable from x.
*/
int length_full1(nodell x)
    requires x::llistR<n,m,R1>@L
    ensures  res = m;
{
 if (x==null) return 0;
 else return length_list(x.val) + length_full1(x.next);
}


/* returns the number of all nodes reachable from x.
*/
int length_full2(nodell x)
    requires x::llistR<n,m,R2>@L
    ensures  res = m;
{
 if (x==null) return 0;
 else return 1 + length_list(x.val) + length_full2(x.next);
}
