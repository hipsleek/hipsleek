/*
pred_prim Map_int<mp1:mapping(int => int), mp2:mapping(int => int)>;
pred_prim Map<int>;

relation  Store_int(mapping(int => int) mapppp1,
                mapping(int => int) mapppp2,
                int key, int val).
relation  Store(mapping(`T3 => `T4) mapppp1,
                mapping(`T3 => `T4) mapppp2,
                `T1 key, `T2 val).
*/
pred_prim Map<idx>;
/*
relation StoreInt(mapping(`T1 => `T2) mp, int idx1, int idx2, `T1 key, `T2 value).
relation Store( mapping(`T3 => `T4) idx1, mapping(`T3 => `T4) idx2, `T3 key, `T4 value).
relation AccessInt(mapping(`T5 => `T6) map, int idx, `T5 key, `T6 value).
*/
relation StoreInt(mapping(`T1 => `T2) mp1,
                  mapping(`T1 => `T2) mp2,
                  `T1 key, `T2 value).
relation Store( mapping(`T3 => `T4) idx1, mapping(`T3 => `T4) idx2, `T3 key, `T4 value).
relation AccessInt(mapping(`T5 => `T6) map, `T5 key, `T6 value).


void update [T7,T8] (ref mapping(`T7 => `T8) mp, `T7 key, `T8 val)
   requires  mp::Map<mp1>
   ensures  mp'::Map<mp2>
            & Store(mp1,mp2,key,val);

`T10 select [T9,T10] (mapping(`T9 => `T10) mp, `T9 key)
   requires mp::Map<mp1>@L & mp1[key] = val //AccessInt(mp1,n,key,val)
   ensures  res = val;

/*

TODO We loose the fact that res should be of type `T10 :

`T10 select$mapping(`T9 => `T10)~`T9 [T9,T10](  mapping(`T9 => `T10) mp,  `T9 key)
static (stk) EBase
   exists (Impl)[mp1:TVar[1840][]]mp:mapping(int => TVar[1840])::Map<mp1:TVar[1840][]>@L&
   mp1:int[][key:int]=val:TVar[1840]&{FLOW,(4,5)=__norm#E}
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}
     EAssume
       emp&res:TVar[1838]=val:TVar[1838]&{FLOW,(4,5)=__norm#E}
       struct:EBase
                emp&res:TVar[1840]=val:TVar[1840]&{FLOW,(4,5)=__norm#E}
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}
{(30,0),(32,22)}
*/

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
