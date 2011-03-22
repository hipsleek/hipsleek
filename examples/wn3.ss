
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

ll<n> == self=null & n=0
        or self::node<_, q> * q::ll<n-1>
        inv n>=0;
 
node list(node l)
 requires l::ll<_>
 ensures res::ll<_>;
{
 node x;
 x=new node(0,l);
 return x;
}

node foo(node y)
 requires y::ll<n> & n>0
 ensures res::ll<_>;
{
 y.val=4;
 node x;
 x=list(y);
 return x;
}
