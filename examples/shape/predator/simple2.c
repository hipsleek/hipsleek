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

void create()
	requires true
	ensures true;
	{
	 node a = malloc();
	 if (a==null) return;
	 node t;
	 node p=a;
	 while(nondeterm()) {
	    p.h = 1;
	    t = malloc();
	    if (t==null) return;
	    p.n = t;
	    p = p.n;
	 }
	 p.h = 1;
	 p.n = null;
	 p = a;
	 while (p!=null) {
	    if (p.h != 1) error();
	    p = p.n;
	 }
	 return;
	}

node malloc ()
 requires true
 ensures res=null or res::node<_, null>;
