bool nondeterm()
 requires true
 ensures !res or res;

data node {
  int h;
  node n;
}

ls1<p> == self=p 
  or self::node<1,q> * q::ls1<p>  
  inv true;
ls2<p> == self=p 
  or self::node<2,q> * q::ls2<p>  
  inv true;
ls3<> == self::ls2<r> * r::node<3,null> 
  inv true;
ls4<> == self::node<3,null> 
  inv true;
ls<> == self::ls1<q> * q::ls2<r> * r::node<3,null> 
  inv true;


int main() 
	requires true
        ensures true;
	{
	  /* Build a list of the form 1->...->1->2->....->2->3 */
	  node a = malloc();
	  if (a == null) return 1;
	  node t;
	  node p;
	  //p=a;
          bind a to (v,next) in {
	   form_node(p,v,next);
	  };
   		dprint;
	while(nondeterm()) 
		requires p::node<_,null>
		ensures p'::node<_,null>; //'
	{
		p.h = 1;
	    t =  malloc();
	    if (t == null) return;
	    p.n = t;
	    p = p.n;
	}

	
	loop2(p,t);
	  p.h = 3;
	dprint;
	  bind a to (v,next) in {
	   form_node(p,v,next);
	  };
 	dprint;
	  loop3(p);  //checking 1' 
	  loop4(p);  //checking 2'
	  if(p.h != 3)
	    return 3; //error
	  return 0;
}

void loop2(ref node p, ref node t)
  requires p::node<_,null>
  ensures p'::node<_,null>; //'
{  
	if(nondeterm()) {
	    p.h = 2;
	    t = malloc();
	    if (t == null) return;
	    p.n = t;
	    p = p.n;
	    loop2(p,t);
	 }
       
}

void loop3(ref node p)
	requires p::ls<>
	ensures p'::ls3<>;//'
{
	if(p.h == 1){
		p=p.n;
		loop3(p);
	}
}

void loop4(ref node p)
	requires p::ls3<>
	ensures p'::ls4<>;//'
{
	if(p.h == 2){
		p=p.n;
		loop4(p);
	}
}

node malloc ()
 requires true
 ensures res=null or res::node<_, null>;

void form_node(ref node x, int v1, node n2)
  requires true
  ensures  x'::node<v1,n2>;
