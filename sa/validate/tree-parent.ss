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
  assume tmp'=p;//'
  if (x.right!=null) 
  	{
//		assert xl'=null;
          trav(x,x.right);
  	}
  if (x.left!=null) {
          trav(x,x.left);
  }
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup


[ G(p_1027,x_1028) ::= 
 x_1028::node<p_1027,left_24_944,right_24_945>@M * G(x_1028,right_24_945) * 
 G(x_1028,left_24_944)&right_24_945!=null & left_24_944!=null
 or x_1028::node<p_1027,left_24_944,right_24_945>@M * G(x_1028,right_24_945)&
    right_24_945!=null & left_24_944=null
 or x_1028::node<p_1027,left_24_944,right_24_945>@M * G(x_1028,left_24_944)&
    left_24_944!=null & right_24_945=null
 or x_1028::node<p_1027,left_24_944,right_24_945>@M&right_24_945=null & 
    left_24_944=null
 ,
 H(p_1023,x_1024) ::= 
 x_1024::node<parent_24_943,left_24_944,right_24_945>@M * 
 H(x_1024,right_24_945)&right_24_945!=null & left_24_944=null & 
 p_1023=parent_24_943
 or x_1024::node<parent_24_943,left_24_944,right_24_945>@M * 
    H(x_1024,left_24_944)&right_24_945=null & left_24_944!=null & 
    p_1023=parent_24_943
 or x_1024::node<parent_24_943,left_24_944,right_24_945>@M * 
    H(x_1024,left_24_944)&right_24_945!=null & left_24_944!=null & 
    p_1023=parent_24_943
 // where is another H(...)?
 or x_1024::node<parent_24_943,left_24_944,right_24_945>@M&
    right_24_945=null & left_24_944=null & p_1023=parent_24_943
 ]



*/
