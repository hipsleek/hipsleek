UTPre@fact fpre(int x).
UTPost@fact fpost(int x).

int fact(int x)
  infer [@term]
  case {
    x = 0 -> requires fpre(x) ensures res>=1 & fpost(x);
    x < 0 -> requires fpre(x) ensures res>=1 & fpost(x);
    x > 0 -> requires Term[x] ensures res>=1 & fpost(x);
  }

{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}

/*
 termAssume 1<=v_int_14_984 & 0<v_int_14_978 & x'=v_int_14_978+1 & 
!(v_bool_13_890') & x'!=0 & !(v_bool_13_890') & x=x' & 0<x & x'!=0 & 
v_int_14_889'=v_int_14_984+1 & 
res=v_int_14_889' & fpost(v_int_14_886') --> fpost(x).

 termAssume 1<=v_int_14_982 & x'=0+1 & !(v_bool_13_890') & x'!=0 & 
!(v_bool_13_890') & x=x' & 0<x & x'!=0 & v_int_14_889'=v_int_14_982+1 & 
res=v_int_14_889' & fpost(0) --> fpost(x).

 termAssume 1<=v_int_14_954 & v_int_14_951<0 & x'=v_int_14_951+1 & 
!(v_bool_13_890') & x'!=0 & !(v_bool_13_890') & x=x' & x<0 & x'!=0 & 
v_int_14_889'=v_int_14_954+1 & 
res=v_int_14_889' & fpost(v_int_14_886') --> fpost(x).

 termAssume x'=0 & x=0 & x=x' & v_bool_13_890' & x'=x' & v_bool_13_890' & 
v_int_13_884'=1 & res=v_int_13_884' --> fpost(x).

 termAssume x'!=0 & x<0 & x=x' & !(v_bool_13_890') & x'!=0 & 
!(v_bool_13_890') & v_int_14_888'=1 & x'=v_int_14_886'+1 & 
v_int_14_886'<0 & fpre(x) --> fpre(v_int_14_886').

*/

