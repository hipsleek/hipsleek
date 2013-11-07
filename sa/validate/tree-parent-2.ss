// simpler tll working example

data node{
	node parent;
	node left;
	node right;
}


tree<p> == self::node<p,null,null>
        or self::node<p,l,r> * l::tree<self> * r::tree<self>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node@NI p, node a).
HeapPred G(node@NI p, node a).

void trav (node p, node x)
 infer [H,G] requires H(p,x) ensures G(p,x);
                             //requires x::tree<p>  ensures x::tree<p>;
{
  node tmp = x.parent;
  node xl = x.left;
  assume tmp'=p;//'
  if (x.right!=null) 
  	{
          
//		assert xl'=null;
          trav(x,x.right);
          assume xl'!=null; //'
          trav(x,x.left);
  	}
  else {
          assume xl'=null; //'
  }
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup


HeapPred H(node@NI p, node a).
HeapPred H6(node p_953, node@NI p).
HeapPred H7(node lf4, node@NI p).
HeapPred H8(node r5, node@NI p).
HeapPred G(node@NI p, node a).


H(p@NI,x) --> x::node<p_953,lf4,r5>@M * H6(p_953,p@NI) * H7(lf4,p@NI) * H8(r5,p@NI),

H8(r5,p@NI)&r5!=null & p=p_953 |#| x::node<p,lf4,r5>@M --> H(x@NI,r5),

H7(lf4,p@NI)&lf4!=null & p=p_953 |#| x::node<p,lf4,r5>@M --> H(x@NI,lf4),

H6(p_953,p@NI) * x::node<p,lf4,r5>@M * G(x@NI,r5) * G(x@NI,lf4)&r5!=null & lf4!=null & p=p_953 --> G(p@NI,x),

  x::node<p,lf4,r5>@M * G(x@NI,r5) * G(x@NI,lf4)&r5!=null & lf4!=null  --> G(p@NI,x),
  H6(p_953,p@NI) & p=p_953 --> G(p@NI,x),

H6(p_953,p@NI) * H7(lf4,p@NI) * H8(r5,p@NI) * x::node<p,lf4,r5>@M&r5=null & lf4=null & p=p_953 --> G(p@NI,x)]

 x::node<p,lf4,r5>@M&r5=null & lf4=null  --> G(p@NI,x)]
 H6(p_953,p@NI) & p=p_953 --> true
 H7(lf4,p@NI) &  lf4=null --> true
 H8(r5,p@NI) & r5=null --> true



[ G(p_1017,x_1018) ::= 
 x_1018::node<p_1017,lf4,r5>@M * G(x_1018,r5) * 
 G(x_1018,lf4)&r5!=null & lf4!=null
 or x_1018::node<p_1017,lf4,r5>@M&r5=null & 
    lf4=null
 ,
 H(p_1013,x_1014) ::= 
 x_1014::node<p_953,lf4,r5>@M * 
 H(x_1014,r5)&r5!=null & lf4=null & 
 p_1013=p_953
 or x_1014::node<p_953,lf4,r5>@M * 
    H(x_1014,lf4)&r5=null & lf4!=null & 
    p_1013=p_953
 or x_1014::node<p_953,lf4,r5>@M * 
    H(x_1014,lf4)&r5!=null & lf4!=null & 
    p_1013=p_953
 or x_1014::node<p_953,lf4,r5>@M&
    r5=null & lf4=null & p_1013=p_953
 ]


*/
