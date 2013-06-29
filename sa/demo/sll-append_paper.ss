data node{
	node next;
}

ll<> == self = null or self::node<q> * q::ll<>;
ls<y> == self = y or self::node<q> * q::ls<y>;
	
PostPred G(node a,node b).
HeapPred H(node a,node@NI b).

void sll_append(node x, node y)
infer [H,G] requires H(x,y) ensures G(x,y);
//requires x::ll<> & x!=null ensures x::ls<y>;
{
	if (x.next!=null) {
            sll_append(x.next,y);
            }
	else 
		{
			x.next = y;
		}
}

/*

Seems correct:

[ H(x_815,y_816) ::=  x_815::node<next_15_792>@M * 
    HP_793(next_15_792,y_816)&true,
 
 G(x_819,y_820) ::=  
     x_819::node<next_15_792>@M * G(next_15_792,y_820)&next_15_792!=null
  or x_819::node<y_820>@M&true
 ,
 HP_793(next_15_817,y_818) ::=  
   next_15_817::node<next_15_792>@M * HP_793(next_15_792,y_818)&true
   or emp&next_15_817=null
 ]




*/