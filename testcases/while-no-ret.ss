int main() {
  int a;
  while (true) {
    a = 1;
  }
  return 0;
}

/*
int main()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)
{
{local: int a
int a
 while (true)
EList
{
{a = 1}
}
(100, ):return 0}
}

void while_3_2$int(  int a)
@ref a
 rec
static (stk) EBase
   emp&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       ref [a]
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(boolean v_bool_3_1828;
(v_bool_3_1828 = true;
if (v_bool_3_1828) [{({a = 1};
{while_3_2$int(a) rec})}]
else []
))}

{(3,2),(5,3)}

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
{((int a;
{while_3_2$int(a)});
(int v_int_6_1829;
(v_int_6_1829 = 0;
ret# v_int_6_1829)))}

{(1,0),(0,-1)}

*/