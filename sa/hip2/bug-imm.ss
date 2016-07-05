
data node {
	int val; 
	node next;	
}

ll<> == self = null
	or self::node<_, r> * r::ll<> 
	inv true;


/* function to delete the node after the head in a circular list */
void delete(ref node x)

	requires x::ll<> & x!=null
	ensures x'::ll<> & x::node<_,null>;

/*

Post-cond has a "conjunction" but this result in
wrong message below:

Exception Failure("The postcondition cannot contain @L heap predicates/data nodes/field annotations\n") Occurred!
(Program not linked with -g, cannot print stack backtrace)


*/

{
	node tmp;
        dprint;
	if (x.next == null) {
		x = null;
                  dprint;
        }
	else
	{
		tmp = x.next;
		x.next=null;
		x = tmp;
                  dprint;
	}
}

