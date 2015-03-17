data node {
	int val; 
	node next; 
}

llN<n> == self=null & n=0
  or self::node<_, p> * p::llN<n-1>
inv true;

llH<v, R:relation(int,int)> == self::node<v, null>
  or self::node<v, q> * q::llH<w, R> & R(v, w)
  inv true;

relation R1(int a, int b).
relation R2(int a, int b).

relation P(int a, int b).
relation Q(int a, int b, int c).

relation P1(int a, int b).
relation Q1(int a, int b, int c).

/*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R1: ( w_641=w_719 & R1(a,w_641)) -->  R1(r1,w_719),
] should be R1: ( w_641 >= w_719 & R1(a,w_641)) -->  R2(r1,w_719),
*************************************/


node ins(node r, node s)
  infer [Q1,R1,R2]
  requires r::llH<a,R1> * s::node<v,null> & /* P1(a,v) & */ r!=null
     ensures  res::llH<r1,R2> & Q1(r1,a,v);
  //Q1(r1,a,v) == (a>=(1+v) & r1=v) | (v>=r1 & a=r1))
{
  if (r.val<= s.val) {
    s.next=r;
    return r;
  } else {
    if(r.next==null) r.next=s;
    else r.next=ins(r.next, s);
    return s;
  }
}

