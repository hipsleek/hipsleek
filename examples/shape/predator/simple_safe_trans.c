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

ls<p> == self=p 
  or self::node<1,q> * q::ls<p>  
  inv true;

int create()
	requires true
        ensures res = 0 or res = 1;
	{
	 node a = malloc();
	 if (a==null) return 1;
	 node t;
	 node p;
	 
	 bind a to (v,next) in {
	   form_node(p,v,next);
	 };
	 loop(p,t);
	 p.h = 1;
	 p.n = null;

	 bind a to (v,next) in {
	   form_node(p,v,next);
	 };
	 loop2(p);
	 return 0;
	}

void loop(ref node p, ref node t)
  requires p::node<_,null>
  ensures p'::node<_,null>; //'
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
  requires p::ls<null>
  ensures p'=null;//'
{ 
      if (p!=null) {
	if (p.h != 1)
	  {
	    return; //error p'!= null
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
