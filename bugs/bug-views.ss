
/*
  SK combinators can be used to represent
  program and have the following syntax

     term ::= apply term term | K | S 

  The combinators can be reduced, as follows:

    K x y ==> x
    S x y z ==> x z (y z)
*/

// we can represent each subexpression
// with following data structure
data anode {
  int val;  // 0-apply; 1-K; 2-S
  anode fn;
  anode arg;
}

/*
   An SK-term can now be captured using
    term ::= apply term term | K | S 
*/

value<n:int,s:int> ==
  self::anode<1,null,null>  // denotes K
  or self::anode<2,null,null>  // denotes S
  or self::anode<0,f,a> * f::anode<1,null,null> * a::value<> // K v
  or self::anode<0,f,a> * f::anode<2,null,null> * a::value<_,_> // S v
  or self::anode<0,f,a> * f::anode<0,f1,a1> * 
  f1::anode<2,null,null> * a1::value<_> * a::value<_,_> // S v1 v2
  inv self!=null;







