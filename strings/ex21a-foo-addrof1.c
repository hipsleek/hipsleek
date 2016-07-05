
void foo(int* x)
/*
  requires x::int*<n>
  ensures x::int*<n+1>;
*/
{
  *x = *x+1;
}


int* foo2(int* x)
/*
  requires x::int*<n>
  ensures x::int*<n> * res::int*<__> ;
*/
{
  x++;
  return x;
}

/*

int_star __pointer_add__int_star__int__$int_star~int(  int_star p,  int i)static  EBase 
   exists (Expl)[](Impl)[val; offset](ex)[]
     p::int_star<val,offset>@M&
   {FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&Term[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       (exists val_48,offset_49,flted_3_47,
       Anon_13: 
         p::int_star<val_48,offset_49>@M * 
         res::int_star<Anon_13,flted_3_47>@M&
       flted_3_47=i+offset & val_48=val & offset_49=offset&
       {FLOW,(4,5)=__norm#E}[]
dynamic  EBase 
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(1,0),(3,66)}

*/
