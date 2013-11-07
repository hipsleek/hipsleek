// simpler tll working example

data node{
	node left;
	node right;
}


tree<> == self::node<_,null>
        or self::node<l,r> * l::tree<> * r::tree<>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a).
HeapPred G(node a).


void trav (node x)
//infer [H,G] requires H(x) ensures G(x);
requires x::tree<>  ensures x::tree<>;
{
  node xl = x.left;
  if (x.right!=null) 
  	{
          
          // assert xl'=null;
          trav(x.right);
          //assert xl'!=null assume xl'!=null; //
          trav(x.left);
  	}
  else {
    ;
    //assert xl'=null assume xl'=null; //
  }
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup

HeapPred H(node a).
HeapPred H0(node lf8).
HeapPred H1(node r9).
HeapPred G(node a).

H(x) --> x::node<lf8,r9>@M * H0(lf8) * H1(r9).

H1(r9)& r9!=null --> H(r9).

H0(lf8)  --> H(lf8) .

x::node<lf8,r9>@M * G(r9) * G(lf8)&r9!=null --> G(x).

H0(lf8) * H1(r9) * x::node<lf8,r9> &r9=null --> G(x).

//H0(lf8) --> true
H1(r9) & r9!=null --> H(r9).
H1(r9) & r9=null --> true

H0(lf8) |#| x::node<r9,lf8>& r9!=null --> H(lf8) .

H0(lf8) |#| x::node<r9,lf8>& r9=null --> true .

H0(lf8) --> H(lf8) |#| x::node<r9,lf8>& r9!=null 
            or emp |#| x::node<r9,lf8>& r9=null 

H1(r9) --> H(r9) & r9!=null or r9=null.


H(x) --> x::node<lf8,r9>@M * H0(lf8) * H1(r9).
   --> x::node<lf8,r9>@M * H0(lf8) * (H(r9) & r9!=null or r9=null).
   -->  x::node<lf8,r9>@M * H0(lf8) * H(r9) & r9!=null
       or  x::node<lf8,null>@M * H0(lf8) .
   -->  x::node<lf8,r9>@M * H(lf8) * H(r9) & r9!=null
       or  x::node<lf8,null>@M .



*/
