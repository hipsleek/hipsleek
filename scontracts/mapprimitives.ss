relation Store(mapping(`T3 => `T4) idx1,
               mapping(`T3 => `T4) idx2,
               `T3 key, `T4 value).

/* relates the type of the two relation parameters*/
relation Type(mapping(`T11 => `T12) mppp1, mapping(`T11 => `T12) mppp2).

pred Map<idx2> == Type(self,idx2);


void update [T7,T8] (ref mapping(`T7 => `T8) mp, `T7 key, `T8 val)
   requires  mp::Map<mp1>
   ensures   (exists mp2: mp'::Map<mp2> & Store(mp1,mp2,key,val));

`T10 select [T9,T10] (mapping(`T9 => `T10) mp, `T9 key)
   requires [val] mp::Map<mp1>@L  & mp1[key] = val
   ensures  res = val;
