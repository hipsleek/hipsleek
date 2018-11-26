relation Store(mapping(`T3 => `T4) idx1,
               mapping(`T3 => `T4) idx2,
               `T3 key, `T4 value).

/* relates the type of the two relation parameters*/
relation Type(mapping(`T11 => `T12) mppp1, mapping(`T11 => `T12) mppp2).

pred Maaaap<idx2> == Type(self,idx2).

pred_prim Map<idx2> inv Type(self,idx2);
pred_prim Mappp<>;
pred_prim SameType<idx2> inv Type(self,idx2);


// (assert (= dest (store src key val)))
// Store(mp1,mp2,key,val)  ==> (assert (= mp2 (store mp1 key val)))

void update [T7,T8] (ref mapping(`T7 => `T8) mp, `T7 key, `T8 val)
   requires  [mp1111] mp::Map<mp1111>
   ensures   (exists mp2: mp'::Map<mp2> & Store(mp1111,mp2,key,val));

`T10 select [T9,T10] (mapping(`T9 => `T10) mp, `T9 key)
   requires [val] mp::Map<mp1>@L  & mp1[key] = val
   ensures  res = val;
