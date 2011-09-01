/* queues represented as a linked list with front and back pointers */

data node {
         int val;
         node next;
}
queue<n> == self = null & n = 0 
           or self::node<_,q> * q::queue<n-1>
           inv n >= 0;
queue2<r,n> == self::node<_, null> & r = self & n = 1
           or self::node<_,q> * q::queue2<r,n-1> & q != null
           inv self != null & r != null & n >= 1;

/* queue<r,n> == lseg<null,n>*/

lseg<p, n> == self=p & n=0
           or self::node<_, r> * r::lseg<p, n-1>
           inv n>=0;

coercion self::lseg<p, n> <- self::lseg<q, n1> * q::lseg<p, n2> & n=n1+n2;//for append3 + append4
//coercion self::lseg<q,n> <- self::lseg<p,n-1> * p::node<_,q>;//for only append3, append4 fails
coercion self::queue2<p,n> <-> self::lseg<p,n-1> * p::node<_,null> ;
//coercion self::queue2<q,n> <- self::queue2<p,n-1> * q::node<_,null> & q = p.next;                                                                             


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

/*function to insert new node at the rear*/
/*NOT WORKING
node append2(node x,node r, int v)
        requires x::queue2<r,n> & n > 0
        ensures res::queue2<_, n+1>;//because of here
{
         node tmp = new node(v,null);
         r.next = tmp;
//         r = r.next;        
         return x;
}*/

void append3 (node x, node r, node v)
        requires x::queue2<r,n> * v::node<_, null>
        ensures x::queue2<v,1+n>;
{
        r.next = v;
}

void append4 (node x, node tx, node y, node ty)
        requires x::queue2<tx,n> * y::queue2<ty,m>
        ensures x::queue2<ty,m+n>;                                                                                                                             
{
        tx.next = y;                                                                                                                          
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