/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null 
	or self::node<_, q> * q::ll<> 
  inv true;

HeapPred P(node x,int r).
HeapPred P1(node x).

int length(node x)
  infer [P1,@classic,@pure_field]
  requires x::ll<>
  //ensures P(x,res);
  ensures P1(x);
/*
requires x::ll<>
  ensures x::ll<> & res>=0;
*/
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex20b.ss

  infer [P1,@classic,@pure_field]
  requires x::ll<>
  //ensures P(x,res);
  ensures P1(x);

# below will need the complex unfolding that Richard is currently doing

[ view P1<>= 
  EList
    :EBase 
       exists (Impl)[q_1631](* lbl: *){285}->(exists Anon_1630: (* lbl: *){285}->
       self::node<Anon_1630,q_1631>@M * q_1631::P1<>@M&self!=null&
       {FLOW,(1,28)=__flow#E}[])
    || :EBase 
          (* lbl: *){286}->self::ll<>@M&self=null&{FLOW,(1,28)=__flow#E}[]
    ]


*/
