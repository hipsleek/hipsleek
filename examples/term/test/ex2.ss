int foo (int x)
requires x>=0
variance [x]
ensures res=0;
{
	if (x == 0) return x;
	else {
		//int x1 = x - 1;
		//assert x'-x1'>0;
		//assert x1'>=0;
		return foo(x-1);
	}
	//return 0;
}

/*

{(1,0),(1,59)}
int foo$int(  int x)
static  true & 0<=x & {FLOW,(13,14)=__norm,}
   EVariance [  x@ 0 ] ==> [  ]
     EAssume 
       true & res=0 & {FLOW,(13,14)=__norm,}
dynamic  
boolean v_bool_6_160;
v_bool_6_160 = {
int v_int_6_155;
v_int_6_155 = 0;
eq___$int~int(x,v_int_6_155)
};
if (v_bool_6_160) LABEL! 4,0: int v_int_6_156;
v_int_6_156 = x;
return v_int_6_156
else LABEL! 4,1: int v_int_11_159;
v_int_11_159 = {
int v_int_11_158;
v_int_11_158 = {
int v_int_11_157;
v_int_11_157 = 1;
minus___$int~int(x,v_int_11_157)
};
foo$int(v_int_11_158) rec
};
return v_int_11_159

boolean eq___$int~int(  int a,  int b)
static  case {a=b -> true & true & {FLOW,(13,14)=__norm,}
                EAssume 
                  true & res & {FLOW,(13,14)=__norm,}
       ;
  a!=b -> true & true & {FLOW,(13,14)=__norm,}
            EAssume 
              true & !res & {FLOW,(13,14)=__norm,}
  }

*/
