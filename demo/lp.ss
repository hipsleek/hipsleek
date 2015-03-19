void lp(ref int i)
 infer [@post_n]
 requires true
 ensures true;
{
   if (i<100) {
      i=i+1;
      lp(i);
   }
}
