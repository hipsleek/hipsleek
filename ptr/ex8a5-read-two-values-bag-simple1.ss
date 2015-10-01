pred_prim read<b:bag(int)>;
pred_prim write<b:bag(int)>;

//pred_prim read<b:int>;

int read_arr(int[] a, int i)
  requires (exists S2: a::read<S>@L & S=union({i},S2))
  ensures  res=a[i];

void write_arr(ref int[] a, int i, int v)
  requires (exists S2: a::write<S>@L & S=union({i},S2))
  ensures  a'[i]=v;  // forall(j. j!=i -> a'[j]=a[j])

int foo2(int[] a)
  requires a::read<{5,4}>@L
  ensures res=a[5]+a[4]+6;
{
  int v=read_arr(a,5);
  int v2=read_arr(a,4);
  return v+6+v2;
}

// can symbolic index be used?
// translate a[i]
int foo3(int[] a,int i)
  requires a::read<{i}>@L
  ensures res=a[i]+6;
{
  int v=read_arr(a,i);
  //int v2=read_arr(a,j);
  return v+6;
}
/*
# ex8a5.ss

Post condition cannot be derived:
  (may) cause:  res=6+(a[i]) |-  res=(a[i])+6. LOCS:[0;25;24;30;26] (may-bug)
*/

/*
# ex8a3.ss -tp oc --ato

# reading only

id: 0; caller: []; line: 13; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@dis_err]
 
checkentail (exists flted_10_38: a::read<flted_10_38>@L&
v_int_13_1387'=5 & flted_10_38={5} & a'=a & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  (exists flted_6_40: a'::read<flted_6_40>@L&
flted_6_40={j_1409} & j_1409=v_int_13_1387'&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?

read set - allowed to read (in - input)
write set - allowed to write (out - output)
read and write set  (in-out or ref)

*/
