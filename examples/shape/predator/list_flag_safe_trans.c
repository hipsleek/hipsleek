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
ls3<> == self::ls1<r> * r::node<3,null> 
  inv true;
ls4<> == self::ls2<r> * r::node<3,null> 
  inv true;
ls5<> == self::node<3,null> 
  inv true;

int main() 
requires true
ensures res = 0 or res = 1;
{
  bool flag = nondeterm();
  node p;
  node a;
  node t;

  /* Build a list of the form x->x->x->...->x->3
   * with x depending on some flag
   */
  a = malloc();
  if (a == null) return 1;
  bind a to (v,next) in {
	   form_node(p,v,next);
	 };
  loop(p,t,flag);
  p.h = 3;
    
  /* Check it */
  bind a to (v,next) in {
	   form_node(p,v,next);
	 };
  if (flag)
    loop3(p);
  else
    loop4(p);
  if (p.h != 3)
    return 3;
  return 0;
}


void loop(ref node p, ref node t, bool flag)
  requires p::node<_,null>
  ensures p'::node<_,null>; //'
{ 
        if(nondeterm()) {
	    if (flag) {
	      p.h = 1;
	    } else {
	      p.h = 2;
	    }
	    /*** TVLA forgets at this point the dependence
		 between p->h and the value of flag        ***/
	    t = malloc();
	    if (t == null) return;
	    p.n = t;
	    p = p.n;
	 }
}

void loop3(ref node p)
	requires p::ls3<>
	ensures p'::ls5<>;//'
{
	if(p.h == 1){
		p=p.n;
		loop3(p);
	}
}

void loop4(ref node p)
	requires p::ls4<>
	ensures p'::ls5<>;//'
{
	if(p.h == 2){
		p=p.n;
		loop4(p);
	}
}


node malloc ()
 requires true
 ensures res=null or res::node<_, null>;

void form_node(node x, int v1, node n2)
  requires true
  ensures  x::node<v1,n2>;
