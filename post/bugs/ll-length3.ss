data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>;

int length(node x)
  infer [@pre_n,@post_n]
  requires x::ll<n>
  ensures x::ll<m>;
{
  if (x == null)
    return 0;
  else
    return 1+length(x.next);
}

/*

Why don't have n in post_1240?
Why don't have pre?

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN pre_1239: ( true) -->  pre_1239(m_1262),
RELDEFN post_1240: ( res=0 & m_1238=0 & pre_1239(m_1238)) -->  post_1240(m_1238,res),
RELDEFN post_1240: ( post_1240(m_1275,v_int_17_1280) & m_1275=m_1238-1 & v_int_17_1280=res-1 &
pre_1239(m_1238)) -->  post_1240(m_1238,res)]
*************************************

!!! new 1 inv(ll): true

!!! new 1 inv(ll): true

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1240(m_1238,res), m_1238=res & 0<=res, true, true)]
*************************************

!!! REL POST :  post_1240(m_1238,res)
!!! POST:  m_1238=res & 0<=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
length$node
 requires x::ll<n> & MayLoop[]
     ensures x::ll<m_1238> & m_1238=res & 0<=res;

*/
