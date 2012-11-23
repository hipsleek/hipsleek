bool nondeterm()
 requires true
 ensures !res or res;

bool error()
 requires false
 ensures true;

data node {
  int h;
  node n;
}

ls<p,n> == self=p & n = 0 
  or self::node<_,q> * q::ls<p,m> & n = m +1  
  inv n >= 0;

void create()
	requires true
        ensures true;
	{
	 node a = malloc();
	 if (a==null) return;
	 node t;
	 node p;
	 bind a to (v,next) in {
	   form_node(p,v,next);
	 };
	 loop(p,t);
	 p.h = 1;
	 p.n = null;
	 //p=a;
	bind a to (v,next) in {
	   form_node(p,v,next);
	 };
	 loop2(p);
	 return;
	}

void loop(ref node p, ref node t)
  requires p::ls<null,n>  & n = 1
  ensures p'::ls<null,n> & n = 1; //'
{ 
        if(nondeterm()) {
	    p.h = 1; 
	    t = malloc(); 
	    if (t==null) return; 
	    p.n = t; 
	    p = p.n; 
	    loop(p,t);
	 }
}

void loop2(ref node p)
  requires p::ls<null,n> & n >= 1 
  ensures p'=null;//'
{ 
      if (p!=null) {
	if (p.h != 1)
	  {
	    p=null;
	    return;
	  }
	   p = p.n;
	   loop2(p);
      }
}


node malloc ()
 requires true
 ensures res=null or res::node<_, null>;

void form_node(node x, int v1, node n2)
  requires true
  ensures  x::node<v1,n2>;
