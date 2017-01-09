bool nondeterm()
 requires true
 ensures !res or res;

data node {
  int h;
  node n;
}

ls<> == self = null 
  or self::node<_,q> * q::ls<>  
  inv true;


int main() 
	requires true
        ensures true;
	{
		node x = null;
		node t = malloc();
		t.n = x;
		x = t;
		t = malloc();
		t.n = x;
		x = t;
t = malloc();
		t.n = x;
		x = t;
		dprint;
  		
	  	return 0;
	}


node malloc ()
 requires true
 ensures res::node<_, null>;

void form_node(ref node x, int v1, node n2)
  requires true
  ensures  x'::node<v1,n2>;
