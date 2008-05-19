
data cell { 
	int val; 
}

data pair { 
	int fst; 
	int snd; 
}

data node {
	int val;
	node next;
}

ll<n,u> == self=null & n=0 & u=1
        or self::node<_, null> & u=2 & n=1
        or self::node<_, q> * q::ll<n-1,_> & q!=null & u=3
        inv n>=0;
 
node list(node l)
 requires l::ll<_,_>
 ensures res::ll<a,b>;
 //ensures res::ll<_,_>;
{
 node x;
 x=new node(0,l);
 dprint;
 return x;
}

node foo(node y)
 requires y::ll<n,m> & m>1
 ensures res::ll<_,_>;
{
 y.val=4;
 node x;
 x=list(y);
 return x;
}
