int main0() {
  while (true) {
    return 1;
  }
  while (true) {
    return 2;
  }
  return 0;
}

/*
int main()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)
{
{ while (true)
EList
{
{(98, ):return 1}
}
 while (true)
EList
{
{(100, ):return 2}
}
(101, ):return 0}
}


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
{(boolean v_bool_2_1865;
(v_bool_2_1865 = true;
if (v_bool_2_1865) [{({(ret_int v_ret_int_3_1864;
(v_ret_int_3_1864 = {((int v_int_3_1863;
v_int_3_1863 = 1);
new ret_int(v_int_3_1863))};
throw v_ret_int_3_1864:{,(23,24)=ret_int#E}))};
{while_2_2$() rec})}]
else []
))}

{(2,2),(4,3)}

void while_5_2$() rec
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
{(boolean v_bool_5_1871;
(v_bool_5_1871 = true;
if (v_bool_5_1871) [{({(ret_int v_ret_int_6_1870;
(v_ret_int_6_1870 = {((int v_int_6_1869;
v_int_6_1869 = 2);
new ret_int(v_int_6_1869))};
throw v_ret_int_6_1870:{,(23,24)=ret_int#E}))};
{while_5_2$() rec})}]
else []
))}

{(5,2),(7,3)}

int main$()
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
{(({while_2_2$()};
{while_5_2$()});
(int v_int_8_1872;
(v_int_8_1872 = 0;
ret# v_int_8_1872)))}
 catch (23,24)=ret_int#E ret_int:f_r_1857 )
        (int v_int_1_1859;
(v_int_1_1859 = bind f_r_1857 to (val_1_1858) [read] in
val_1_1858;
ret# v_int_1_1859))

{(1,0),(0,-1)}
*/