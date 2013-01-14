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
Why does some formula like tmp_28'=null appear twice?

dprint: err-1-dupl.ss:25: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]
[
 Label: 
 State:or[x'::node<v_560,flted_9_559>@M[Orig]&flted_9_559=null & mi=v_560 
  & x=x' & flted_9_559=tmp_28' 
  & tmp_28'=null & b_29' 
  & tmp_28'=null&{FLOW,(22,23)=__norm}[]
 ; 
   x'::node<mi_565,p_566>@M[Orig] * p_566::llMM<mi2_567>@M[0][Orig]
  &mi=mi_565 & x=x' & p_566=tmp_28' 
  & tmp_28'!=null & !(b_29') 
  & tmp_28'!=null&{FLOW,(22,23)=__norm}[]
 ]

 Seems like case-condition added to post-condition:::

  x'::node<mi_565,p_566>@M[Orig] * p_566::llMM<mi2_567>@M[0][Orig]&
  mi=mi_565 & x=x' & p_566=tmp_28' & tmp_28'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: true
conseq:
 EAssume 186::
   emp&213::!(res) & tmp_28'!=null&{FLOW,(22,23)=__norm}[]

*/

