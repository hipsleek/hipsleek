
data CDL{}

pred_prim CNT<n:int,id:int>;
pred_prim downd<c:CDL,id:int>;       /* used by the dynamic sync */
pred_prim downv<c:CDL,n:int,id:int>; /* used by virt sync: n is used for the initialization of the latch */
pred_prim await<c:CDL,id:int>;       /* used by both dyn and virt sync */

void AWAIT(CDL c)
  requires [idd] c::CNT<0,idd>
  ensures  c::CNT<(-1),idd>;
  requires [iddd] c::CNT<(-1),iddd>
  ensures  c::CNT<(-1),iddd>;

void DOWN(CDL c)
  requires c::CNT<n,idddd> & n>0
  ensures  c::CNT<n-1,idddd>;

/* ******************* normalization lemmas ******************* */
lemma_norm   "ACC"  self::CNT<n,id> * self::CNT<m,id> & m>=0 & n>=0-> self::CNT<m+n,id>.
lemma_norm   "REL1" self::Chan{@S downd<cc,id>;;%R}<> -> self::Chan{@S %R}<> * cc::CNT<1,id>.
lemma_norm@2 "REL2" self::Chan{@S downv<cc,n,id>;;%R}<> -> self::Chan{@S %R}<> * cc::CNT<n-1,id>.
lemma_norm   "REL3" self::Chan{@S downv<cc,n,id>;;%R}<> * cc::CNT<pp,id>& pp<n -> self::Chan{@S %R}<> * cc::CNT<pp-1,id>.
lemma_norm   "REL4" self::Chan{@S await<cc,id>;;%R}<> * cc::CNT<n,id> & (n=0|n=(0-1)) -> self::Chan{@S %R}<> * cc::CNT<(-1),id>.


/* ******************* verification lemmas ******************* */
/* lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>; */
/* lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>; */
