/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi> == self::node<v,null> & mi=v  
  or self::node<mi, p> * p::llMM<mi2> 
  //& mi=min(v,mi2) 
  //& v<=mi2
inv self!=null;


node sel(ref node x)
     requires x::llMM<mi> 
     ensures  true
     ;
{
  node tmp;
  tmp =x.next;
  dprint;
  bool b=(tmp==null);
  b=b;
  dprint;
  if (b)
    { dprint;
      return tmp;
    }
  else {
    dprint;
    return tmp;
    }
}

      /*
       Why does some formula appear twice?
Successful States:
[
 Label: [(129::,0 ); (129::,0 )]
 State:x'::node<v_560,flted_9_559>@M[Orig]&flted_9_559=null & mi=v_560 & x=x' & flted_9_559=tmp_28' 
     & tmp_28'=null & v_bool_24_534' 
     & tmp_28'=null & v_bool_24_534'
     &{FLOW,(22,23)=__norm}[]
       es_var_measures: MayLoop

 ]
      */
