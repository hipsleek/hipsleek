/* void main() */
/* /\* */
/*   requires Term */
/*   ensures true; */
/* *\/ */
/*   infer[@term] */
/*   requires true */
/*   ensures true; */
/* { */
/*      int[] a = new int[1024]; */
/*      int i = __VERIFIER_nondet_int(); */
/*      if (0 <= i && i < 1024) { */
/*         if (a[0] == 1 && a[i] == 2) { */
/*            //dprint; */
/*            assert(i' > 0); */
/*            loop(i, -i); */
/*            //dprint; */
/*            //assert(false); */
/*         } */
/*      } */
/* } */

void main()
  infer[@term]
  requires true
  ensures true;
{
  int i = __VERIFIER_nondet_int();
  if (0 <= i && i < 1024) {
    if (i > 0) {
      loop(i, -i);
    }
  }
}

void loop (int i, int j)
/*
     case {
          i < 0 -> requires Term ensures true;
          i >= 0 -> case {
               j > 0 -> requires Term[i] ensures true;
               j <= 0 -> requires Loop ensures false;
          }
     }
*/
  infer[@term]
  requires true
  ensures true;
{
  if (i < 0) return;
  else loop(i - j, j);
}
