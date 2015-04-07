/* singly linked lists */

/* representation of a node */
data node {
  int val;
  node next;
}

/* view for a singly linked list */

ll<S> == self = null & S = {}
  or self::node<v, q> * q::ll<S1> & S = union(S1, {v});

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1 & S=union(S1, {v});*/

/* append two singly linked lists */
void append(node x, node y)
  requires x::ll<S1> * y::ll<S2> & x != null
  ensures x::ll<S> & S = union(S1, S2);
{
   if (x.next==null)
    {
      x.next = y;
      //dprint;
      //assume false;
    }
   else
     {
       //assume false;
       append(x.next, y);
       dprint;
     }
}

/*
# ex2-app-bags.ss

!!! **cfout.ml#423:important variables:[S1,S2,x,y,x',v_1519,q_1520,S_1541]
!!! **cfout.ml#425:exists variables:
 [S2_1536,S1_1535,S1_1521,y',v_bool_26_1478']

dprint before: ex2-app-bags.ss:36: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:(exists S_1541: x'::node<v_1519,q_1520> * q_1520::ll{}<S_1541>
 & S_1541=union(S1_1535,S2_1536) & S2_1536=S2 & S1_1535=S1_1521 
 & S1=union(S1_1521,{v_1519}) & x'=x & y'=y & x!=null 
& q_1520!=null & !(v_bool_26_1478')
&{FLOW,(4,5)=__norm#E}[]

 ]

dprint(simpl): ex2-app-bags.ss:32: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:(exists S_1541: x'::node<v_1519,q_1520> * q_1520::ll{}<S_1541>
 & exists(S1_1521: S_1541=union(S1_1521,S2) 
 & S1=union(S1_1521,{v_1519}))  & y'=y & x'=x & x!=null 
 & q_1520!=null
 & {FLOW,(4,5)=__norm#E}[]

 ]

# Why isn't v_bool_26_1478' removed by simplifier? (FIXED by Long)
  it has been renamed as v_bool_26_1478_1542'

# similarly for the following vars:
  S2_1536,S1_1535,S1_1521

dprint after: ex2-app-bags.ss:36: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:x'::node<v_1519,q_1520> * q_1520::ll{}<S_1541>
 & y=y_1543' & x=x' & !(v_bool_26_1478_1542') & x'!=null 
 & q_1520!=null & S_1541=union(S1_1535_1545,S2_1536_1546) 
 & S2_1536_1546=S2 & S1_1535_1545=S1_1521_1544 
 & S1=union(S1_1521_1544,{v_1519})
 &{FLOW,(4,5)=__norm#E}[]

EXPECTING
=========
existential should be eliminated where possible.
 [S2_1536,S1_1535,S1_1521,y',v_bool_26_1478']
(i) rename S1_1521 --> S1_1535
(ii) rename S1_1536 --> S2
(iii) elim   # & !(v_bool_26_1478') // to delete
(iv) x!=null is redundant


Successful States:
[
 Label: [(,1 ); (,2 )]
 State:(exists S_1541: x'::node<v_1519,q_1520> * q_1520::ll{}<S_1541>
 & S_1541=union(S1_1535,S2) 
 & S1=union(S1_1535,{v_1519}) & x'=x & y'=y & x!=null 
 & q_1520!=null 
 &{FLOW,(4,5)=__norm#E}[]

 ]


Successful States:
[
 Label: [(,1 ); (,2 )]
 State:
(exists S_1541: 
  x'::node<v_1519,q_1520> * q_1520::ll{}<S_1541>
  &  S_1541=union(S1_1535,S2_1536) 
  & S2_1536=S2 & S1_1535=S1_1521 
  & S1=union(S1_1521,{v_1519}) 
  & x'=x & y'=y & x!=null & q_1520!=null & !(v_bool_22_1478')&{FLOW,(4,5)=__norm#E}[]

 ]

dprint after: ex2-app-bags.ss:32: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:x'::node<v_1519,q_1520> * q_1520::ll{}<S_1541>
  &y=y' & x=x' & x'!=null & q_1520!=null 
  & S_1541=union(S1_1542,S2) & S1=union(S1_1542,{v_1519})
 &{FLOW,(4,5)=__norm#E}[]

 Why isn't exists S_1541 renamed?

 Why is there a fresh S1_1542? when there is no need
 to provide a fresh name.



 ]

*/
