hip_include 'scontracts/mapprimitives.ss'

global mapping(int => int) mpp;

global int yyy;
/*
int goo()
    requires yyy>0
    ensures  yyy'=0;
{
 yyy = 0;
 return 0;
}

*/
/** why goo works fine while for foo HIP complains about not finding mp? */
/** !! see the error below !! */

int foo() //(ref mapping(int => int) mp)
   requires mp::Map<mp9>@L
   ensures  res=9;
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  dprint;
  return x+yyy;
}


/**

../hip test-map-21-bug.ss -dre "trans_proc\|rename_exp\|subid"

!!!! below mp should have been changed to mp_21

(==iastUtil.ml#997==)
rename_exp(IastUtil)@13
rename_exp(IastUtil) inp1 :{local: int x
mp[0] = 9
int x = mp[0]
dprint
return x + yyy}
rename_exp(IastUtil) inp2 :({ __get_char, __plus_plus_char, __write_char, aalloc___,
acquire, add___, alloc_str, array_get_elm_at___1d, array_get_elm_at___2d, delete_ptr,
 div2, div3, div4, div___, divs___, eq___, finalize, finalize_str, foo, fork, get_cha
r, gt___, gte___, init, join, land___, lor___, lt___, lte___, max, min, minus___, mod
___, mp, mp_21, mult___, mults___, neq___, not___, plus_plus_char, pow___, rand_bool,
 rand_int, release, res, select, update, update___1d, update___2d, write_char, yyy,yy
_22 },[(mp,mp_21),(yyy,yyy_22)])
rename_exp(IastUtil)@13 EXIT:{local: int x
mp[0] = 9
int x = mp[0]
dprint
return x + yyy_22}

*/
