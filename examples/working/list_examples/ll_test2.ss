/* NOT WORKING... */

/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)

	requires x::ll<L1> & len(L1) > a & a > 0 
	ensures x::ll<L2> & exists (La, Lm, Lb: L1 = app(La, Lm, Lb) & len(Lm) = 1);

{
	if (a == 1) {
		x.next = x.next.next;
	} else {
      delete(x.next, a-1);
	}	
}

/* function to delete the a-th node in a singly linked list */
/* looks like an infinite loop */
void delete4(node x, int a)

  requires x::ll<L1> & len(L1) > a & a > 0 
     ensures x::ll<L2> & exists (La, Lm, Lb: L1 = app(La, Lm, Lb) & len(Lm) = 1 & len(L2)=len(L1)-1 );

     /* works */
     /* ensures x::ll<L2> &  len(L2) = len(L1)-1; */
     /* infinite loop? */
     /* ensures x::ll<L2> & exists (La,Lb,v: L1 = app(La,[|v|],Lb) & L2=app(La,Lb) & len(L2) = len(L1)-1); */
     /* ensures x::ll<L2> & L1 = app(La,[|v|],Lb) & L2=app(La,Lb) & len(L2) = len(L1)-1 & len(L2)=len(La)+len(Lb); */
     /* ensures x::ll<L2> & exists (La,Lb,v: L1 = app(La,[|v|],Lb) & L2=app(La,Lb) & len(L2) = len(L1)-1 & len(L2)=len(La)+len(Lb)); */
{
	if (a == 1) {
		x.next = x.next.next;
	} else {
		delete4(x.next, a-1);
	}	
}
