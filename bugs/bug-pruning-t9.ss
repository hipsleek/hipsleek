
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
term<> ==
     self::anode<0,f,a> * f::term<> * a::term<>
  or self::anode<1,null,null> // denotes K
  or self::anode<2,null,null> // denotes S
  inv self!=null;

/*
  An interpreter can be used to reduce an
  SK-term into a value of the following form.
   value ::=  K | S | K value | S value
              | S value value
  Note that none of the SK reduction rules
  can be applied to above value.

  Provide a predicate that captures the
  final value for such a reduction.
*/

value<n:int> ==
  self::anode<1,null,null>  // denotes K
  or self::anode<2,null,null>  // denotes S
  or self::anode<0,f,a> * f::anode<1,null,null> * a::value<> // K v
  or self::anode<0,f,a> * f::anode<2,null,null> * a::value<> // S v
  or self::anode<0,f,a> * f::anode<0,f1,a1> * 
      f1::anode<2,null,null> * a1::value<> * a::value<> // S v1 v2
  inv self!=null;

lemma  self::term<> <- self::value<>;

bool isApply(anode t)
  requires t::anode<v,_,_>@L
  ensures true & (v=0 & res | v!=0 & !res);
{
  return t.val == 0;
}

// write strongest postcondition for method below
bool isCombK(anode t)
  requires t::anode<v,_,_>@L
  ensures true & (v=1 & res | v!=1 & !res);
{
  return t.val == 1;
}

// write strongest postcondition for method below
bool isCombS(anode t)
  requires t::anode<v,_,_>@L
  ensures true & (v=2 & res | v!=2 & !res);
{
  return t.val == 2;
}




// using your value predicate, verify the
// cloning method below
anode clone (anode t)   // cloning a value
 requires t::value<>@L
 ensures  res::value<>;
{
 anode tmp1, tmp2, tmp3;
 if (isApply(t)) {
      tmp1 = clone(t.arg);
      if (isCombK(t.fn)) {
	return new anode(0, new anode(1, null, null), tmp1);		
      }
      else if (isCombS(t.fn)) {
	return new anode(0, new anode(2, null, null), tmp1);		     
      }
      else {
        tmp2 = clone(t.fn.arg);
        tmp3 = new anode(0, new anode(2, null, null), tmp2); 
	return new anode(0, tmp3, tmp1);
     }
 }
 else return new anode(t.val, null, null);
}

// using your value predicate, verify the
// corectness of the reduction method below
anode reduction (anode t)
  requires t::term<>
  ensures  res::value<>;
{
 anode val1, val2, val11, val2c;
 anode tmp1, tmp2, tmp3;
 if (isApply(t)) {
   // apply
   val1 = reduction(t.fn);
   val2 = reduction(t.arg);
   t.fn = val1;
   t.arg = val2;
   if (isCombK(val1)) return t;
   else if (isCombS(val1)) return t;
   else { 
     // val1 is an apply
     val11 = val1.fn;
     if (isCombK(val11)) return val1.arg;
     else if (isCombS(val11)) return t;
     else {
       // val3 is an apply
       // it has to be an (S w1)
       val2c = clone(val2);
       tmp1 = new anode(0,val11,val2);
       tmp2 = new anode(0,val1.arg,val2c);
       t.fn = tmp1;
       t.arg = tmp2;
       return reduction(t);
     }
   }
 } else return t; 
}






