/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/*
TODO : emp is currently
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 1::
                              EXISTS(emp: true&emp&{FLOW,(20,21)=__norm})[])
dynamic  EBase false&false&{FLOW,(20,21)=__norm}[]
{(17,0),(19,14)}
*/

void disp_node(node x)
  requires x::node<_,_>
  ensures emp;

//@ -tp mona --classic
void disp_ll(node x)
  requires x::ll<n>
  ensures emp;
{
  if (x!=null) {
    disp_ll(x.next);
    disp_node(x);
  }
}
