data anode {
  int val;  // 0-apply; 1-K; 2-S
  anode fn;
  anode arg;
}


termK<n> ==
     self::anode<0,f,a> * f::termK<n1> * a::termK<n2> & n=1+n1+n2
  or self::anode<1,null,null> & n=0  // denotes K
  inv self!=null & n>=0;


valueK<> ==
  self::anode<1,null,null>  // denotes K
  or self::anode<0,f,a> * f::anode<1,null,null> * a::valueK<> // K v
  inv self!=null;

lemma self::valueK<> -> self::termK<>;

anode clone (anode t)
requires t::valueK<>@I
ensures  res::valueK<>;

bool isApply(anode t)
  requires t::anode<v,_,_>@I
  ensures true & (v=0 & res | v!=0 & !res);
{
  return t.val == 0;
}

bool isCombK(anode t)
  requires t::anode<v,_,_>@I
  ensures true & (v=1 & res | v!=1 & !res);
{
  return t.val == 1;
}

bool isCombS(anode t)
  requires t::anode<v,_,_>@I
  ensures true & (v=2 & res | v!=2 & !res);
{
  return t.val == 2;
}


anode reduction (anode t)

requires t::termK<n>
variance (1) [n]
ensures  res::valueK<> ;

{
 anode val1, val2, val11, val2c;
 anode tmp1, tmp2, tmp3;
	bool b = isApply(t);
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
       anode temp = reduction(t);
       return temp;
     }
   }
 } else return t; 
}






