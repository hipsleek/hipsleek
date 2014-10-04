data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>;

int length(node x)
  infer [@post_n]
  requires x::ll<n>
  ensures x::ll<m>;
{
  if (x == null)
    return 0;
  else
    return 1+length(x.next);
}

/*

Why don't have n in post_1239?

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN post_1239: ( res=0 & m_1238=0) -->  post_1239(m_1238,res),
RELDEFN post_1239: ( post_1239(m_1270,v_int_17_1274) & m_1270=m_1238-1 & v_int_17_1274=res-1) -->  post_1239(m_1238,res)]
*************************************

!!! new 1 inv(ll): true

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1239(m_1238,res), m_1238=res & 0<=res, true, true)]
*************************************

!!! REL POST :  post_1239(m_1238,res)
!!! POST:  m_1238=res & 0<=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
length$node
 requires x::ll<n> & MayLoop[]
     ensures x::ll<m_1238> & m_1238=res & 0<=res;

*/
