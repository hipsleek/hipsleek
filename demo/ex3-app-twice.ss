data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;


void append(node x, node y)
  requires x::ll<nnn> * y::ll<mmm> & x!=null //nnn>0
  ensures x::ll<eee>& eee=nnn+mmm;

node appendthree(node x, node y,node z)
  requires x::ll<nnn> * y::ll<mmm> * z::ll<kkk> & nnn>0
  ensures x::ll<eee>& eee=nnn+mmm+kkk;
{
  append(x,y);
  dprint;
  append(x,z);
  dprint;
  return x;
}

/*
# ex3-app-twice.ss

node appendthree$node~node~node(  node x,  node y,  node z)static  EBase exists (Expl)[](Impl)[nnn; mmm; kkk](ex)[]x::ll{}<nnn> * 
       y::ll{}<mmm> * z::ll{}<kkk>&0<nnn&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume 
                   (exists eee: x::ll{}<eee>&eee=kkk+nnn+mmm&
                   {FLOW,(4,5)=__norm#E}[]


Why are there nnn,mmm,kkk>=0 in post-checking?
Above post did not have it

id: 10; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail (exists eee_1535: x'::ll{}<eee_1535>&res=x' & 0<=mmm_1529 & 0<=nnn_1528 & 
eee_1535=mmm_1529+nnn_1528 & 0<=eee_1534 & 0<=kkk & mmm_1529=kkk & 
nnn_1528=eee_1534 & 0<=mmm_1522 & 0<=nnn_1521 & eee_1534=mmm_1522+nnn_1521 & 
0<=nnn & 0<=mmm & mmm_1522=mmm & nnn_1521=nnn & x'=x & y'=y & z'=z & 0<nnn&
{FLOW,(4,5)=__norm#E}[]
 |-  (exists eee_1519: x::ll{}<eee_1519>&0<=nnn & 0<=mmm & 0<=kkk & eee_1519=kkk+
nnn+mmm&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   emp&res=x' & 0<=mmm_1529 & 0<=nnn_1528 & eee_1536=mmm_1529+nnn_1528 & 0<=eee_1534 & 0<=kkk & mmm_1529=kkk & nnn_1528=eee_1534 & 0<=mmm_1522 & 0<=nnn_1521 & eee_1534=mmm_1522+nnn_1521 & 0<=nnn & 0<=mmm & mmm_1522=mmm & nnn_1521=nnn & x'=x & y'=y & z'=z & 0<nnn&{FLOW,(4,5)=__norm#E}[]
   ]

*/
