
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
 & forall (l: l notin Bp | k >= l) & forall (r: r notin Bp | k >= r)
inv true;
	
heapt<k:int,B:bag> == self = null
	or self::node<k,p,q> * p::heapt<kp,Bp> * q::heapt<kq,Bq>
inv true;
*/

HeapPred H(node a).
HeapPred G(node a).

void heapify(node x) 
 infer [H,G] requires H(x)
 ensures G(x);

/*
 requires x::tree<S,B> & x!=null
 ensures x::tree<S,B>;

 infer [H,G] requires H(x)
 ensures G(x);
*/
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
   }
   if (s!=null) {
    if (s.key> x.key) {
       int t=s.key;
       s.key= x.key;
       s.key=t;
       heapify(s);
  }}
 }
}

/*
 id: 40; caller: []; line: 35; classic: false; kind: BIND; hec_num: 5; evars: []; infer_vars: [H,G,HP_840,HP_841]; c_heap: emp
 checkentail HP_840(left_24_838) * HP_841(right_24_839) * 
x::node<key_24_837,left_24_838,right_24_839>@M[Orig]&x=x' & 
left_24_838!=null & !(v_bool_24_818') & left_24_838!=null & 
!(v_bool_24_818') & right_24_839=null & v_bool_27_794' & right_24_839=null & 
v_bool_27_794' & left_24_838=s_31' & s_31'!=null & v_bool_34_817' & 
s_31'!=null & v_bool_34_817'&{FLOW,(22,23)=__norm}[]
 |-  s_31'::node<key_35_795',left_35_796',right_35_797'>@L[Orig]&true&
{FLOW,(1,25)=__flow}[]. 
hprel_ass: [ HP_840(left_24_838)&
  left_24_838!=null --> left_24_838::node<key_35_902,left_35_903,right_35_904>@M * 
  HP_905(left_35_903) * HP_906(right_35_904)&true,
 HP_841(right_24_839)&right_24_839=null --> emp&true]
res:  [
  x::node<key_24_837,left_24_838,right_24_839>@M[Orig] * HP_905(left_35_903) * HP_906(right_35_904) * left_24_838::node<key_35_902,left_35_903,right_35_904>@M[Orig]&x=x' & left_24_838!=null & !(v_bool_24_818') & left_24_838!=null & !(v_bool_24_818') & right_24_839=null & v_bool_27_794' & right_24_839=null & v_bool_27_794' & left_24_838=s_31' & s_31'!=null & v_bool_34_817' & s_31'!=null & v_bool_34_817' & key_35_795'=key_35_902 & left_35_796'=left_35_903 & right_35_797'=right_35_904&{FLOW,(22,23)=__norm}[]
  ]


--------------
 id: 112; caller: []; line: 21; classic: false; kind: POST; hec_num: 5; evars: []; infer_vars: [H,G,HP_840,HP_841]; c_heap: emp
 checkentail HP_840(left_24_838) * HP_841(right_24_839) * 
x::node<key_24_837,left_24_838,right_24_839>@M[Orig]&left_24_838=null & 
v_bool_24_818' & left_24_838=null & v_bool_24_818'&{FLOW,(22,23)=__norm}[]
 |-  G(x)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ HP_841(right_24_839) * x::node<key_24_837,left_24_838,right_24_839>@M&
  left_24_838=null --> G(x)&true,
 HP_840(left_24_838)&left_24_838=null --> emp&true]
res:  [
  emp&v_bool_24_818' & v_bool_24_818'&{FLOW,(22,23)=__norm}[]
  ]

*/
