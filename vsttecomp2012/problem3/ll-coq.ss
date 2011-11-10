/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<"n":n,"l":L1> == self = null & [
         "n": n=0;  "l":L1 = [||]]
  or self::node<v, r> * r::ll<n1,L2> & 
   ["n": n=1+n1;
   "l": L1 = v:::L2 ]
  inv true & ["n":n>=0] ;

/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<n1,L1> * y::ll<n2,L2> & ["n":n1>0 ]
  ensures x::ll<r, L> & ["n":r=n1+n2; 
                         "l":L = app(L1, L2)] ;

{
	if (x.next == null) {
		x.next = y;
	} else {
		append(x.next, y);
	}
}

node append2(node x, node y)

  requires x::ll<n1,L1> * y::ll<n2,L2> 
  ensures res::ll<r, L> & ["n":r=n1+n2; 
                           "l":L = app(L1, L2)] ;


node add_front(int i, node x)
  requires x::ll<n,L>
  ensures res::ll<m,L1> & ["n":m=n+1; 
                           "l": L1=i:::L];
{
  return new node(i,x);
}

node add_back(int i, node x)
  requires x::ll<n,L>
  ensures res::ll<m,L1> & ["n": m=n+1;
                           "l": L1=app(L, [|i|] )] ;
{
  return append2(x,new node(i,null));
}


node get_tail(int i, node x)
  requires x::ll<n,L> & ["n":n>0]
  ensures x::node<v,res>*res::ll<m,L1> & ["n":m=n-1; 
         "l": v=head(L) & L1=tail(L)] ;
/*
  // below cannot be proven by Coq
  requires [v,L1] x::ll<n,L> & ["l":L=v:::L1]
  ensures x::node<v,res>*res::ll<m,L1> & ["n":m=n-1
        ] ;
*/
{
  return x.next;
}

