data node {
  int val;
  node next;
}

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p> 
  inv n>=0;

clist<n> ==
  self::node<v, q> * q::lseg<n-1, self>
  inv n>0;

/*
lemma self::clist<n> <- self::lseg<n-1, q> * q::node<v, self>;
lemma self::lseg<n, q> <- self::lseg<n-1, p> * p::node<v, q>;
lemma self::node<v, q> * q::lseg<n, self> -> q::node<v1, s> * s::lseg<n, q>;
*/


int length (node x)
/*
  infer [@term]
  requires x::clist<n>@L
  ensures true;

  infer [@term]
  requires x::lseg<n,null>@L
  ensures res=n;
*/
  infer [@term]
  requires x::lseg<n,null>
  ensures x::lseg<n,null> & res=n;
{
  if (x == null)
    return 0;
  else
    return 1 + length(x.next);
}
/*
# clist2.ss

  infer [@term]
  requires x::lseg<n,null>
  ensures x::lseg<n,null> & res=n;

Why only one relational assumption inferred?

*****************************
*** TERMINATION INFERENCE ***
*****************************
Temporal Assumptions:
 termAssume x=flted_32_1370 & flted_32_1370=null & x'=x & x'=null & 
v_bool_35_1251' & v_int_36_1244'=0 & res=v_int_36_1244' & n=0 & 
exists(n_62:n_62=0) & x=flted_33_60 --> lengthpost_1243(n).


Base/Rec Case Splitting:
[	length: [[1] n=0@B]
]
Termination Inference Result:
length:  requires x::lseg<n,flted_32_61> & flted_32_61=nullcase {
                                                    n=0 -> requires emp & Term[62,1]
 ensures 
                                                    x::lseg<n_62,flted_33_60> & n_62=n & 
                                                    res=n & flted_33_60=null; 
                                                    }

Termination checking result: SUCCESS

*/
