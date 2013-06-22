
data node {
 int key;
 node left;
 node right;
}

/*
relation keys(node x, int k, bag B) == (x = null & B = {}) 
	| x!=null & keys(l,kl,Bl) & keys(r,kr,Br) & B = union(Bl,Br,{k}).
	
tree<S,B> == self=null & S={} & B = {}
 or self::node<k,p,q>*p::tree<Sp,Bp>*q::tree<Sq,Bq> 
 & S = union(Sp,Sq,{self}) & B = union(Bp,Bq,{k})
 & forall (l: l notin Bp | k >= l) & forall (r: r notin Bq | k >= r)
inv true;
*/

heapt<B:bag> == self = null & B={}
	or self::node<k,p,q> * p::heapt<Bp> * q::heapt<Bq>
      & B = union(Bp,Bq,{k})
      & forall (l: l notin Bp | l <= k) & forall (r: r notin Bq | r <= k)
inv true;


/*heapmax<m,B:bag> == self = null & B={} //& m =-\inf
      or self::node<k,p,q> * p::heapmax<mp,Bp> * q::heapmax<mq,Bq> & m = k
      & B = union(Bp,Bq,{k}) & m >= mp & m >= mq
//    & forall (l: l notin Bp | k >= l) & forall (r: r notin Bq | k >= r)
inv true;
*/

HeapPred H(node a).
HeapPred G(node a).

void heapify(node x)
/*  requires x::node<v,p,q> * p::heapmax<mp,B1> * q::heapmax<mq,B2>
  ensures x::heapmax<m,B> & B = union(B1,B2,{v}) 
& m >= mp & m >= mq & m >= v;
*/ 
requires x::node<v,p,q>*p::heapt<B1>*q::heapt<B2>
// & forall (l: l notin B1 | v >= l) 
// & forall (r: r notin B2 | v >= r)
ensures x::heapt<B> & B=union(B1,B2,{v});

/*
requires x::heapt<k,B> & x!= null & keys(x,k,B)
ensures x::heapt<k,B> & keys(x,k,B);

 requires x::tree<S,B> & x!=null
 ensures x::tree<S,B>;

 infer [H,G] requires H(x)
 ensures G(x);*/
{
  node s;
  if (x.left==null) s=x.right;
  else 
  {
   if (x.right==null) s=x.left;
   else {
    node lx=x.left;
    node rx=x.right;
    if (lx.key < rx.key) s=rx;
    else s =lx;
   }}
   if (s!=null) {
    if (s.key > x.key) {
       int t=s.key;
       s.key= x.key;
       x.key=t;
       heapify(s);
  }
 }
  //  dprint;
}
