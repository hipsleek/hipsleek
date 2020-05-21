int main4() {
  while(true) {
    return 1;
    dprint;
  }
  return 2;
}

/*
pip:
int main4()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)
{
{ while (true)
EList
{
{(98, ):return 1
dprint}
}
(99, ):return 2}
}


pcp:
void while_2_2$() rec
static (stk) EBase
   emp&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(boolean v_bool_2_1864;
(v_bool_2_1864 = true;
if (v_bool_2_1864) [{({((ret_int v_ret_int_3_1863;
(v_ret_int_3_1863 = {((int v_int_3_1862;
v_int_3_1862 = 1);
new ret_int(v_int_3_1862))};
throw v_ret_int_3_1863:{,(23,24)=ret_int#E}));
dprint)};
{while_2_2$() rec})}]
else []
))}

{(2,2),(5,3)}

int main4$()
static (stk) EBase
   emp&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
try
{({while_2_2$()};
(int v_int_6_1865;
(v_int_6_1865 = 2;
ret# v_int_6_1865)))}
 catch (23,24)=ret_int#E ret_int:f_r_1856 )
        (int v_int_1_1858;
(v_int_1_1858 = bind f_r_1856 to (val_1_1857) [read] in
val_1_1857;
ret# v_int_1_1858))

{(1,0),(0,-1)}




dprint(simpl): loop-ret-int.ss:8: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]
 Escaped States:
 [

  Try-Block:0::
  [
   Path: [(,1 )]
   State:  (exists v_int_7_1897': v_ret_int_7_1898'::ret_int<v_int_7_1897'>@M&
v_bool_6_1899' & MayLoop[] & v_int_7_1897'=1 & v_int_7_1897'=res &
eres=v_ret_int_7_1898'&{FLOW,(23,24)=ret_int#E}[])
          es_gen_impl_vars(E): []
          es_heap(consumed): emp
   ]
  ]
*/