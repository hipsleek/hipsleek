data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

relation P(int n,int m).
relation Q(int n, int m).

node zip(node x, node y)
  infer [P,Q]
  requires x::ll<n> * y::ll<m> & P(n,m)
  ensures res::ll<n> & Q(n,m,res);
{
  if (x==null) return null;
  else return new node(x.val+y.val,zip(x.next,y.next));
}

/*
# ex21-11-zip.ss

Why mismatched in relation parameter for Q not detected!

Need to simplify pure part of pre/post..

zip$node~node
 EBase exists (Expl)[](Impl)[n; m](ex)[]x::ll{}<n> * y::ll{}<m>&((m!=0 | 
       1>n)) & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists n_1407: res::ll{}<n_1407>&n_1407=n & 0<=n & 0<=m & 
           (((1<=n_1407 & n_1407<=m & res!=null) | (res=null & n_1407<=0)))&
           {FLOW,(4,5)=__norm#E})[]

GOT: {[0,m]: 0 <= m} union {[n,m]: 0 <= n && 1 <= m}

Expect: n<=m

Top-down fix point was constructed for Q.
I think it should be constructed for P from:

[RELDEFN P: ( P(n,m) & 1<=n & 1<=m & n_1462=n-1 & m_1463=m-1) 
     -->  P(n_1462,m_1463),
RELASS [P]: ( P(n,m)) -->  (m!=0 | 1>n),

RELDEFN Q: ( n=0 & res=null & 0<=m & P(n,m)) -->  Q(n,m,res),
RELDEFN Q: ( 1<=n_1462 & v_node_19_1476!=null & 0<=m_1463 & 
Q(n_1462,m_1463,v_node_19_1476) & P(n,m) & m=1+m_1463 & res!=null & n=n_1462+
1) -->  Q(n,m,res),
RELDEFN Q: ( v_node_19_1476=null & n_1462=0 & 0<=m_1463 & 
Q(n_1462,m_1463,v_node_19_1476) & P(n,m) & m=1+m_1463 & res!=null & n=1) -->  Q(n,m,res)]



Q:={[n,m] -> [NODres] -> []: ((((( (exists (n_1407:((1<=n_1407 && n_1407<=m) || n_1407<=0)))  && n=0) && NODres<=0) && 0<=m) || (( (exists (NODv_node_19_1476:( (exists (m_1463:(( (exists (n_1462:(n_1462=0 && Q(n_1462,m_1463,NODv_node_19_1476))))  &&  (exists (n_1407:((1<=n_1407 && n_1407<=1+m_1463) || (n_1407<=0 && 0<=m_1463)))) ) && m=1+m_1463)))  && NODv_node_19_1476<=0)))  && n=1) && NODres>0)) || (( (exists (NODv_node_19_1476:( (exists (m_1463:(( (exists (n_1462:(n_1462+1=n && Q(n_1462,m_1463,NODv_node_19_1476))))  &&  (exists (n_1407:((1<=n_1407 && n_1407<=1+m_1463) || (n_1407<=0 && 0<=m_1463)))) ) && m=1+m_1463)))  && NODv_node_19_1476>0)))  && 2<=n) && NODres>0))
};
TD:=topdown(Q, 3, SimHeur);
TD;

*/
