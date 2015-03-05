/* --ann-vp --classic

 this should detect leakage of variable permission

*/
hip_include 'extra_prelude.ss'
//hip_include `extra-prelude.ss`

void inc7(int i)
 requires @full[i]
 ensures  true; //'@full[i] &
{
  i++;
}


void inc8(int i)
 requires @full[i]
 ensures  @full[i]; //'@full[i] &
{
  i = 5;
}


void main()
 requires true
 ensures  true; //'@full[i] &
{
  int y=3;
  dprint;
  inc8(y);
  dprint;
}



/* 
# ex35d2-vp-post-err.ss --ann-vp



vperm_rm_prime@11
vperm_rm_prime inp1 : U@full[y_36']
vperm_rm_prime@11 EXIT: N@full[y_36]

Why is it normalized but still a prime present
at N@full[y_36']?

combine_vperm_sets@12
combine_vperm_sets inp1 :[ N@zero[y_36]; N@full[y_36']]
combine_vperm_sets@12 EXIT: N@full[y_36']@zero[y_36]




*/
