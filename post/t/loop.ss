
int PastaA1_main()
  infer [@post_n]
  requires true
  ensures true;
//ensures res=10;
{
  int x;
  x=10;
  int y = 0;
    while (y < x) 
      infer [@post_n]
      requires true
      ensures true;
    {
      y++;
    }
  return y; 
}

/*
# loop.ss

    while (y < x) 
      infer [@post_n]
      requires true
      ensures true;
    {
      y++;
    }

Two problems:

(i) Parameters x,y are passed by ref.
    Only y need to be pass-by-ref

(ii) We need to include x',y' in pass-by-ref
     EAssume ref [x_36;y_37]
     emp&post_1188(x_36,y_37)&{FLOW,(4,5)=__norm}[]

   Correct solution in # loop1.ss
      requires true
      ensures (y<x & y'=x & x'=x | y>=x & y'=y & x'=x);


void f_r_1163_while_9_4$int~int(  int x_36,  int y_37)
@ref x_36, y_37
 rec
static  EInfer @post[]
   EBase emp&{FLOW,(4,5)=__norm}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm}[]
                   EAssume ref [x_36;y_37]
                     emp&{FLOW,(4,5)=__norm}[]
                     
dynamic  EBase hfalse&false&{FLOW,(4,5)=__norm}[]
{(boolean v_bool_9_1171;
(v_bool_9_1171 = {lt___$int~int(y_37,x_36)};
if (v_bool_9_1171) [{({(int v_int_9_1170;
v_int_9_1170 = {{((int v_int_14_1168;
v_int_14_1168 = y_37);
(y_37 = {((int v_int_14_1169;
v_int_14_1169 = 1);
add___$int~int(y_37,v_int_14_1169))};
v_int_14_1168))}})};
{f_r_1163_while_9_4$int~int(x_36,y_37) rec})}]
else []
))}

!!! proc_specs:[ EInfer @post[post_1188]
   EBase emp&{FLOW,(4,5)=__norm}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm}[]
                   EAssume ref [x_36;y_37]
                     emp&post_1188(x_36,y_37)&{FLOW,(4,5)=__norm}[]
                     ]

 */
