bool rand() 
 requires true
  ensures res  or !res;

int foo(int x)
  requires true
  ensures res=x+a & a>0;
{
  int t = x+1;
  int rr,xx;
  if (rand() || x==0) return t;
  else {
    xx = 1+foo(x-1);
    rr = 1+foo(x-1);
    dprint;
    return rr;
  }
}

/*

int foo$int(  int x) rec
static  :EBase emp&{FLOW,(24,25)=__norm}[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume 
                    (exists a: emp&res=a+x & 0<a&{FLOW,(24,25)=__norm})[]

 Label: [(,1 ); (,2 )]
 State:emp&x=x' & t_33'=1+x' & !(v_boolean_11_948) & x'!=0 & 
 !(v_boolean_11_949) & x'!=0 & !(v_bool_11_893') & !(v_boolean_11_949) & !(v_boolean_11_948) & !(v_bool_11_893') & x'=v_int_13_962+1 & 0<a_961 
& xx_35'=a_961+v_int_13_962+1 & x'=v_int_14_982+1 & 0<a_981 
& rr_34'=a_981+v_int_14_982+1&{FLOW,(24,25)=__norm}[]
*/

