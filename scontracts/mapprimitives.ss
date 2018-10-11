pred_prim Map<idx>;
relation Store(mapping(`T3 => `T4) idx1,
               mapping(`T3 => `T4) idx2,
               `T3 key, `T4 value).

/* relates the type of the two relation parameters*/
relation Type(mapping(`T11 => `T12) mp1, mapping(`T11 => `T12) mp2).


void update [T7,T8] (ref mapping(`T7 => `T8) mp, `T7 key, `T8 val)
   requires [mp2] mp::Map<mp1>
   ensures       mp'::Map<mp2> & Store(mp1,mp2,key,val);

`T10 select [T9,T10] (mapping(`T9 => `T10) mp, `T9 key)
   requires [val] mp::Map<mp1>@L & Type(mp,mp1) & mp1[key] = val
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
