data anode {
  int val;  // 0-apply; 1-K; 2-S
  anode fn;
  anode arg;
}

allowed<> ==
     self::anode<0,f,a> * f::allowed<> * a::allowed<>
  or self::anode<1,null,null>  // denotes K
  or self::anode<2,null,null>  // denotes S
  inv self!=null;

combK<> ==
  self::anode<1,null,null> 
  inv self!=null;

combS<> ==
  self::anode<2,null,null> 
  inv self!=null;

value<> ==
  self::anode<1,null,null>  // denotes K
  or self::anode<2,null,null>  // denotes S
  or self::anode<0,f,a> * f::combK<> * a::value<> // K v
  or self::anode<0,f,a> * f::combS<> * a::value<> // S v
  or self::anode<0,f,a> * f::anode<0,f1,a1> * 
      f1::combS<> * a1::value<> * a::value<> // S v1 v2
  inv self!=null;
//lemma self::value<> -> self::allowed<>;

anode reduction (anode t)
requires t::allowed<>
ensures t::allowed<> * res::value<>;
{
 anode val1, val2;
 anode tmp, tmp_fn, tmp_arg;      
 if (t.val == 0) {                          // apply
   val1 = reduction(t.fn);
   //assert t'::allowed<>; 
   val2 = reduction(t.arg);
   if (val1.val == 0) {
      if (val1.fn.val == 1)                 // val1 = K v
        return val1.arg;                 
      else {
	    if (val1.fn.val == 2)           // val1 = S v
	          {tmp = val1.fn; 
		   //assert tmp'::combS<>; 
		   //assert val2'::value<>; 
		   return new anode(0, tmp, val2);}        

	     else // (val1.fn.val == 0)
	     if (val1.fn.fn.val == 2)        // val1 = ((S v) v)
                 {tmp_fn = new anode(0, val1.arg, val2);
		  tmp_arg = new anode(0, val1.fn.arg, val2);
		  //assert tmp_arg'::allowed<>;
		  assume val2'::allowed<>; 	  
		  tmp =  new anode (0, tmp_fn, tmp_arg); 
		  return reduction(tmp);
		 }

	    else                             
	    {assume false; return t;}
	 //else {assume false; return t;}
     }
    }
    else
        {assume false; return t;}
  }
  assume false; return t;  //(fn.val == 1 || fn.val == 2) 
      
}



