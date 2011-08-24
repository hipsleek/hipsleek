/* queues represented as a linked list with front and back pointers */

data node {
         int val;
         node next;
}
queue<n> == self = null & n = 0 
           or self::node<_,q> * q::queue<n-1>
           inv n >= 0;
/*queue<r,n> == self::node<_, null> & r = self & n = 1
           or self::node<_,q> * q::queue<r,n-1>
           inv n >= 1;
*/
/* queue<r,n> == lseg<null,n>

lseg<p, n> == self=p & n=0
           or self::node<_, r> * r::lseg<p, n-1>
           inv n>=0;
*/

void dispose(node x)
          requires x::node<_,_>
          ensures true;

/*function to insert new node at the rear*/
void append(node x, int v)
          requires x::queue<n> & n > 0
          ensures x::queue<n+1>;
{
          if(x.next == null)
                   x.next = new node(v, null);
          else
                   append(x.next,v); 
}

/*function to remove a node at front*/
void serve(ref node x)
          requires x::queue<n> & n > 1 
          ensures x'::queue<n-1>;
{
         node tmp = x;
         x = x.next;
         dispose(tmp);
}