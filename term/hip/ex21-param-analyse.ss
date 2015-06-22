
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
     ensures true;
{

  if (x>0 || y>0) {
    dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex21.ss

This produced:

  x=(b'-a')+x'+1 & y=(y'-b')+a'+1 & a'<=(b'+x') & b'<=(y'+a') 
   & R(x,y,a',b') -->  R(x',y',a',b'),
  y=(y'-b')+a'+1 & x=(b'-a')+x'+1 & (y'+a')<b' & a'<=(b'+x') 
   & R(x,y,a',b') -->  R(x',y',a',b'),
  x=(b'-a')+x'+1 & y=(y'-b')+a'+1 & (b'+x')<a' & b'<=(y'+a') 
   & R(x,y,a',b')) -->  R(x',y',a',b')]

which seem sufficient to analyse that

   a,b are unchanged across recursion  a'=a, b'=b
   x,y are inductively changed by x'=nxt1(x); y'= nxt2(y)


Earlier context were as follows. Are they similar to above?

  State:
      emp&a'=a & b'=b & y'=y & x=x' & 1<=y & R(x,y,a,b) & 1<=x'
    CtxOR
      emp&a'=a & b'=b & y'=y & x=x' & y<=0 & R(x,y,a,b) & 1<=x'&
    CtxOR
      emp&a'=a & b'=b & x=x' & y'=y & x'<=0 & 1<=y & R(x,y,a,b)&

# Why are there so many cases? Are below the same?


Can we use it to analyze that:

id: 48; caller: []; line: 13; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ R]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail emp&
v_bool_10_1204' & v_boolean_10_1250 & 0<y_1299 & v_boolean_10_1251 & 
x_1275=x & y_1299=y & a'=a & b'=b & R(x,y,a,b) & 0<x_1275 & 
x'+1+b'=a'+x_1275 & y'+1+a'=b'+y_1299 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&R(x',y',a',b')&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN R: ( x=(b'-a')+x'+1 & y=(y'-b')+a'+1 & a'<=(b'+x') & b'<=(y'+a') & R(x,y,a',b')) -->  R(x',y',a',b')]

id: 50; caller: []; line: 13; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ R]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail emp&
v_bool_10_1204' & v_boolean_10_1252 & y_1298<=0 & not(v_boolean_10_1253) & 
x_1274=x & y_1298=y & a'=a & b'=b & R(x,y,a,b) & 0<x_1274 & 
x'+1+b'=a'+x_1274 & y'+1+a'=b'+y_1298 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&R(x',y',a',b')&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN R: ( y=(y'-b')+a'+1 & x=(b'-a')+x'+1 & (y'+a')<b' & a'<=(b'+x') & R(x,y,a',b')) -->  R(x',y',a',b')]

id: 52; caller: []; line: 13; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ R]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail emp&
v_bool_10_1204' & not(v_boolean_10_1254) & v_boolean_10_1255 & 0<y_1297 & 
x_1273=x & y_1297=y & a'=a & b'=b & R(x,y,a,b) & x_1273<=0 & 
x'+1+b'=a'+x_1273 & y'+1+a'=b'+y_1297 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&R(x',y',a',b')&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN R: ( x=(b'-a')+x'+1 & y=(y'-b')+a'+1 & (b'+x')<a' & b'<=(y'+a') & R(x,y,a',b')) -->  R(x',y',a',b')]

 */
