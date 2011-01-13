int Ack(int m, int n)
requires m>=0 & n>=0
variance (1) [m,n]
ensures res>0;
{
	if (m==0) return n+1;
	else if (n==0) {
		return Ack(m-1,1);
	} else {
		return Ack(m-1, Ack(m,n-1));
	}
}

/*
int Ack$int~int(  int m,  int n)
static  EBase true & 0<=m & 0<=n & {FLOW,(14,15)=__norm,}
         EVariance (1) [  m@ 0  n@ 0 ] ==> [  ]
           EAssume 
             true & 0<res & {FLOW,(14,15)=__norm,}
dynamic  
boolean v_bool_6_172;
v_bool_6_172 = {
int v_int_6_157;
v_int_6_157 = 0;
eq___$int~int(m,v_int_6_157)
};
if (v_bool_6_172) LABEL! 8,0: int v_int_6_159;
v_int_6_159 = {
int v_int_6_158;
v_int_6_158 = 1;
add___$int~int(n,v_int_6_158)
};
return v_int_6_159
else LABEL! 8,1: boolean v_bool_7_171;
v_bool_7_171 = {
int v_int_7_160;
v_int_7_160 = 0;
eq___$int~int(n,v_int_7_160)
};
if (v_bool_7_171) LABEL! 9,0: int v_int_8_164;
v_int_8_164 = {
int v_int_8_163;
v_int_8_163 = {
int v_int_8_161;
v_int_8_161 = 1;
minus___$int~int(m,v_int_8_161)
};
int v_int_8_162;
v_int_8_162 = 1;
Ack$int~int(v_int_8_163,v_int_8_162) rec
};
return v_int_8_164
else LABEL! 9,1: int v_int_10_170;
v_int_10_170 = {
int v_int_10_169;
v_int_10_169 = {
int v_int_10_165;
v_int_10_165 = 1;
minus___$int~int(m,v_int_10_165)
};
int v_int_10_168;
v_int_10_168 = {
int v_int_10_167;
v_int_10_167 = {
int v_int_10_166;
v_int_10_166 = 1;
minus___$int~int(n,v_int_10_166)
};
Ack$int~int(m,v_int_10_167) rec
};
Ack$int~int(v_int_10_169,v_int_10_168) rec
};
return v_int_10_170

*/
