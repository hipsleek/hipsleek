pred_prim Map<mp1:mapping(int => int), mp2:mapping(int => int)>;
relation  Store_int(mapping(int => int) mapppp1,
                mapping(int => int) mapppp2,
                int key, int val).
relation  Store(mapping(`T1 => `T2) mapppp1,
                mapping(`T1 => `T2) mapppp2,
                `T1 key, `T2 val).


void update [T1,T2] (ref mapping(int => int) map, int key, int val)
   requires  map::Map<map1,map2>
   ensures  map'::Map<map2,map3>
            & Store(map3,
                    map2,
                    key,val);

`T2 select [T1,T2] (mapping(`T1 => `T2) map, `T1 key)
   requires [val] map::Map<map1,map2>@L & map2[key]=val
   ensures  res = val;

/*

pred_prim Map<mp1,mp2>;
relation  Store(mapping(`T3 => `T4) mapppp1,
                mapping(`T3 => `T4) mapppp2,
                `T3 key, `T4 val).

void update [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key, `T2 val)
   requires  map::Map<map1:mapping(`T1 => `T2),map2:mapping(`T1 => `T2)>
   ensures  map'::Map<map2:mapping(`T1 => `T2),map3:mapping(`T1 => `T2)>
            & Store(map2,
                    map3,
                    key,val);
*/
/*
   requires map::Map<map1,map2>
   ensures  map'::Map<map2,map3> & Store(map2,map3,key,val);
*/

/*
Store(map1,map2,key,val)  => Z3: (= (store map1 key val) map2)
*/

/*
`T2 select [T1,T2] (mapping(`T1 => `T2) map, `T1 key)
   requires [val] map::Map<map1,map2>@L & map2[key]=val
   ensures  res = val;
*/
/*
void delete [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key)
   requires true
   ensures  map'[key]=ZERO;
*/
