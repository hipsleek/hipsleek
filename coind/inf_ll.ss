/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

inf_ll<> == self::node<_, q> * q::inf_ll<> 
  inv true;

ll<n> == self=null & n=0 or
      self::node<_, q> * q::ll<n-1> 
  inv n>=0;


node gen_inf ()
  requires true & Loop
  ensures res::inf_ll<>;
{
  node t = gen_inf();
  dprint;
  return new node(0,t);
}

node gen_inf2 ()
  requires true & Loop
  ensures false;
{
  node t = gen_inf2();
   dprint;
  return new node(0,t);
}


node gen_inf3 ()
  requires true 
  ensures res::ll<n> & n=\inf;
{
  node t = gen_inf3();
  dprint;
  return new node(0,t);
}


node gen_inf3a ()
  requires true 
  ensures res::ll<n> & n<\inf;
{
  node t = gen_inf3a();
  dprint;
  return new node(0,t);
}

node gen_inf4 ()
  requires true & Loop
  ensures true;
{
  node t = gen_inf4();
  dprint;
  return new node(0,t);
}

node gen_inf2a ()
  requires true & MayLoop
  ensures false;
{
  node t = gen_inf2a();
   dprint;
  return new node(0,t);
}

node main ()
  requires true & Loop
  ensures false;
{
  node t = gen_inf2a();
   return t;
}

node gen_inf2b ()
  requires true & MayLoop
//ensures res::ll<n> & n=\inf;
  ensures res=null;
{
  node t = gen_inf2b();
   dprint;
  return new node(0,t);
}
