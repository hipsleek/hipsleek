/*
MAY
  LOR
   OK
   MUST: 0<=index & index<3 & index=2 & index=index & i_20'=2+index &
v_int_13_470'=i_20' & res=v_int_13_470' |-  res<3
   loc: 14, 17, 19, 21, 12 (optimal: 15, 17)
 */
/*
int testme1(int index)
requires index >=0 & index <3
 ensures res >=0 & res<3;
{
  int i;
  if (index != 2)
    {
      index = 1;
    }
  else index = index +4;

  i = index + 3;
  //dprint;
  return i;
}
*/

int testme2(int index)
requires index >=0 & index <3
 ensures res >=0 & res<3;
{
   if (index < 2)
    {
      index = index + 2;
    }
  else index = 3;

  return index;
}

/*
int testme2(int index)
requires index >=0 & index <3
 ensures res >=0 & res<3;
{
  int i;
  if (index != 2)
    index = 1;
  else index = index +4;

  i = index;
  //dprint;
  return i+2;
}
*/
/*
ante:  0<=index & index<3 &
index=2 & 116::!(v_bool_15_469') & index=index &
!(v_bool_15_469') &
i_20'=2+index & 
v_int_21_470'=i_20' & res=v_int_21_470'
locle: errors/hip/err1.ss_11_9;errors/hip/err1.ss_11_21;
errors/hip/err1.ss_15_15;
./prelude.ss_110_4 (neg);./prelude.ss_6_10 (add);
errors/hip/err1.ss_21_9;errors/hip/err1.ss_21_2;
 */
