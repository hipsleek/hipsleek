bool nondeterm()
 requires true
 ensures !res or res;

data node {
   int h;
   node n;
}

ls<p> == self=p 
  or self::node<1,q> * q::ls<p>  
  inv true;

void main() 
  requires true
  ensures true;
{
  node t;
  node p = null;
  loop(t,p);
  loop2(p);
}

void loop(ref node t, ref node p)
  requires p::ls<null>
  ensures p'::ls<null>; //'
{ 
        if(nondeterm()) {
	    t = malloc();
	    if (t == null) return;
	    t.h = 1;
	    t.n = p;
	    p = t;
	    loop(t,p);
	 }
}

void loop2(ref node p)
  requires p::ls<null>
  ensures p'=null;//'
{ 
	if(p!=null) {
	    if (p.h != 1) {
	      return;
	    }
	    p = p.n;
	    loop2(p);
	}
}


node malloc ()
 requires true
 ensures res=null or res::node<_, null>;

