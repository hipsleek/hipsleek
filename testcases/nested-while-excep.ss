int main1() {
  while (true) {
    return 1;
    while (true) {
      return 2;
    }
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
{(98, ):return 1
 while (true)
EList
{
{(100, ):return 2}
}}
}
(101, ):return 0}
}


void while_4_4$() rec
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
{(boolean v_bool_4_1869;
(v_bool_4_1869 = true;
if (v_bool_4_1869) [{({(ret_int v_ret_int_5_1868;
(v_ret_int_5_1868 = {((int v_int_5_1867;
v_int_5_1867 = 2);
new ret_int(v_int_5_1867))};
throw v_ret_int_5_1868:{,(23,24)=ret_int#E}))};
{while_4_4$() rec})}]
else []
))}

{(4,4),(6,5)}

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
{(boolean v_bool_2_1870;
(v_bool_2_1870 = true;
if (v_bool_2_1870) [{({((ret_int v_ret_int_3_1863;
(v_ret_int_3_1863 = {((int v_int_3_1862;
v_int_3_1862 = 1);
new ret_int(v_int_3_1862))};
throw v_ret_int_3_1863:{,(23,24)=ret_int#E}));
{while_4_4$()})};
{while_2_2$() rec})}]
else []
))}

{(2,2),(7,3)}

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
{({while_2_2$()};
(int v_int_9_1871;
(v_int_9_1871 = 0;
ret# v_int_9_1871)))}
 catch (23,24)=ret_int#E ret_int:f_r_1856 )
        (int v_int_1_1858;
(v_int_1_1858 = bind f_r_1856 to (val_1_1857) [read] in
val_1_1857;
ret# v_int_1_1858))

{(1,0),(0,-1)}
*/