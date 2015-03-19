/* --ann-vp

*/


void inc5(int i)
 requires @value[i]
 ensures  @full[i]; //'@full[i] &
{
  i++;
}


void inc6(int i)
 requires @value[i]
 ensures  true; //'@full[i] &
{
  i++;
}

void inc7(int i)
 requires @full[i]
 ensures  true; //'@full[i] &
{
  i++;
}


/* 
# ex35d1-vp-post-err.ss --ann-vp

void inc5(int i)
 requires @value[i]
 ensures  @full[i]; //'@full[i] &
{
  i++;
}

valid but expect post error

need to add @ver_post prior to post-checking..
use Wrapper.ml code & add this at typechecker.ml


*/
