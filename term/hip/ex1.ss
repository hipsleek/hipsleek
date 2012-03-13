data node {
	int val; 
	node next;	
}

//logical int c1,c0,p1,p2;

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
	inv n >= 0;

node app2(node x, node y)
 requires x::ll<n> * y::ll<m> & n  >= 0
 variance [n]
 ensures res::ll<n+m>;
{
 if (x==null) return y;
 else {
   node w=x.next;
   //assert w'::ll<a> & n>a; //'
   //assert n>=1;
   return new node(x.val,app2(w,y));
 }
}


int length (node xs)
 requires xs::ll<n>
 case {
  xs=null -> variance [0] ensures n=0 & res=0; // fails without n=0!
  xs!=null -> variance [1,n] ensures xs::ll<n> & res=n;
 }
{
  if (xs==null) return 0;
  else {
         node tmp = xs.next;
         int r = 1+length(tmp);
         //dprint;
         return r;
  }
}


