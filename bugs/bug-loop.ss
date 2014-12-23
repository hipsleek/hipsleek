data node { int val ; node next }


ll<> == self::node<_, null> ;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::ll_tail2<r, n-1> * r::ll<> & r!=null
 inv n>=1;


//pred ll_tail<tx, n> == self::node<_, null> & tx=self & n=1
	//or self::ll_tail<_, r> * r::ll_tail<tx, n-1> & r!=null.
	
// loops on self::ll_tail , most likely due to the search for view_data_name
