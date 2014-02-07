data node {
 int val;
 node next;
}

lseg<n, p,S> ==
  self = p & n = 0 & S={}  or
  self::node<v, q> * q::lseg<n-1, p,S1> & S=union({v},S1) 
 inv n>=0;

/*
clist<n> ==
 self::node<v, q> * q::lseg<n-1, self> 
inv n>0;
lemma self::clist<n>  <- self::lseg<n-1, q> * q::node<v, self>;
*/

lemma self::lseg<n,q,S> & S=union({v},S1)  
     <- self::lseg<n-1,p,S1> * p::node<v, q>;

lemma self::lseg<n,q,S> & x \in S  S=union({v},S1)  
     <- self::lseg<n-1,p,S1> * p::node<v, q>;

node remove (node x, int v)
 requires x::node<val, p> * p::lseg<n1, x,S1>
 case {
    val = v -> ensures x::node<val, p> 
                      * p::lseg<n1, x,S1> & res=p;
    val != v -> 
      case {
         (v notin S1) -> ensures false;
         (v in S1) -> ensures x::node<val, q> 
           * q::lseg<n1-1,x,S2> & S1=union({v},S2);
    }
 }
{
 if (x == null)
  return null;
 else {
 if (x.val == v) {
  return x.next;
  } else {
     dprint;
     node tmp = remove(x.next, v);
     assume false;
     x.next = tmp;
     assume false;
    return x;
 }
 }
}
