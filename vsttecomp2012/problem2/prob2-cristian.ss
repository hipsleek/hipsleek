data anode {
  int val;  // 0-apply; 1-K; 2-S
  anode fn;
  anode arg;
}

allowed<> ==
     self::anode<0,f,a>*f::allowed<>*a::allowed<>
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
