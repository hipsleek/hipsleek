data node {
	int val;
	node next;
}

lseg<n,p> == case {
    n=0 -> [] self=p ;
    n!=0 -> [] self::node<_, q> * q::lseg<n-1,p>;
  } inv n>=0;

clist<n> == self::node<_,p>*p::lseg<n-1,self>
  inv self!=null & n>0;

lemma_safe self::lseg<n,p> & n=a+b & a,b>=0 
  <-> self::lseg<a,q>*q::lseg<b,p>;

lemma_safe self::clist<n> <- self::lseg<n-1,q>*q::node<_,x>;

void append(node x, node y)
  requires x::clist<n> & Loop
  ensures false;
{
  if (x.next!=null) append(x.next, y);
  else x.next = y;
}

/*

# ex5-lemma-proof

. Why is it Lemma_16, not Lemma_17?
. Why this cannot be proven?
. Why is Lemma_14 sufficient?


Entailing lemma lem_16: Fail. (no cex)(must) cause: lor[ emp&flted_17_1472=0 & self_lem_16=q_1473 & flted_17_1472+1=n & 
Anon_1476=Anon_1471 & p_1477=x_1474&{FLOW,(6,10)=__Error#E}[], q_1493::node<Anon_1491,x_1494>&flted_17_1492!=0 & flted_8_1488+
1=flted_17_1492 & p_1487=q_1493 & flted_17_1492+1=n & Anon_1496=Anon_1489 & 
p_1497=q_1490&{FLOW,(6,10)=__Error#E}[]]

Entailing lemma lem_14: Valid.

Valid Lemmas : [lem_14:<==>] added to lemma store.

Checking procedure append$node~node... 


*/
