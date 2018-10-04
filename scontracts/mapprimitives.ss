pred_prim Map_int<mp1:mapping(int => int), mp2:mapping(int => int)>;
pred_prim Map<mp1, mp2>;

relation  Store_int(mapping(int => int) mapppp1,
                mapping(int => int) mapppp2,
                int key, int val).
relation  Store(mapping(`T3 => `T4) mapppp1,
                mapping(`T3 => `T4) mapppp2,
                `T1 key, `T2 val).


void update [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key, `T2 val)
   requires  map::Map<map1:mapping(`T1 => `T2),map2>
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


/*
AFTER UNIFICATION

map2:mapping(`T3 => `T4) ==> map2:mapping(`T1 => `T2) ? NO
map1: Unk                ==> map2:mapping(`T3 => `T4) ? YES

void update$mapping(`T1 => `T2)~`T1~`T2 [T1,T2](  mapping(`T1 => `T2) map,  `T1 key,  `T2 val)
@ref map:mapping(`T1 => `T2)

static (stk) EBase
   exists (Impl)[map1:Unknown;
   map2:mapping(`T3 => `T4)]map:mapping(`T1 => `T2)::Map<map1:Unknown,map2:mapping(`T3 => `T4)>@M&
   {FLOW,(4,5)=__norm#E}
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}
     EAssume
       ref [map:mapping(`T1 => `T2)]
       (exists map2_90:mapping(`T3 => `T4),
       map3:mapping(`T3 => `T4): map':mapping(`T1 => `T2)::Map<map2_90:mapping(`T3 => `T4),map3:mapping(`T3 => `T4)>@M&
       Store:RelT([])(map3:mapping(`T3 => `T4),map2:mapping(`T3 => `T4),key:`T1,val:`T2) &
       map2_90:mapping(`T3 => `T4)=map2:mapping(`T3 => `T4)&
       {FLOW,(4,5)=__norm#E})
       struct:EBase
                (exists map2_91:mapping(`T3 => `T4),
                map3:mapping(`T3 => `T4): map':mapping(`T1 => `T2)::Map<map2_91:mapping(`T3 => `T4),map3:mapping(`T3 => `T4)>@M&
                Store:RelT([])(map3:mapping(`T3 => `T4),map2:mapping(`T3 => `T4),key:`T1,val:`T2) &
                map2_91:mapping(`T3 => `T4)=map2:mapping(`T3 => `T4)&
                {FLOW,(4,5)=__norm#E})
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}
{(12,0),(17,29)}


*/


/**
Why boolean below? (at normalization)

static (stk) EBase
   exists (Impl)[map2:mapping(`T3 => `T4)](exists flted_13_91:boolean:
   map:mapping(`T1 => `T2)::Map<flted_13_91:boolean,map2:mapping(`T3 => `T4)>@M&
   ((flted_13_91:boolean & map1:mapping(`T1 => `T2):mapping(`T1 => `T2)) |
    (!(flted_13_91:boolean) & !(map1:mapping(`T1 => `T2):mapping(`T1 => `T2))))&
   {FLOW,(4,5)=__norm#E})
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}
     EAssume
       ref [map:mapping(`T1 => `T2)]
       (exists map2_92:mapping(`T3 => `T4),
       map3:mapping(`T3 => `T4): map':mapping(`T1 => `T2)::Map<map2_92:mapping(`T3 => `T4),map3:mapping(`T3 => `T4)>@M&
       Store:RelT([])(map3:mapping(`T3 => `T4),map2:mapping(`T3 => `T4),key:`T1,val:`T2) &
       map2_92:mapping(`T3 => `T4)=map2:mapping(`T3 => `T4)&
       {FLOW,(4,5)=__norm#E})
       struct:EBase
                (exists map2_93:mapping(`T3 => `T4),
                map3:mapping(`T3 => `T4): map':mapping(`T1 => `T2)::Map<map2_93:mapping(`T3 => `T4),map3:mapping(`T3 => `T4)>@M&
                Store:RelT([])(map3:mapping(`T3 => `T4),map2:mapping(`T3 => `T4),key:`T1,val:`T2) &
                map2_93:mapping(`T3 => `T4)=map2:mapping(`T3 => `T4)&
                {FLOW,(4,5)=__norm#E})
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}
{(12,0),(17,29)}



*/
