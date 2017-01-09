void main()
     requires Term
     ensures true;
{
     int[] a = new int[1024];
     int i;
     if (0 <= i && i < 1024) {
        if (a[0] == 1 && a[i] == 2) {
           dprint;
           assert(i' > 0);
           loop(1, i);
           dprint;
           assert(false);
        }
     }
}

void loop (int i, int j)
     case {
          i < 0 -> requires Term ensures true;
          i >= 0 -> case {
               j > 0 -> requires Term[i] ensures true;
               j <= 0 -> requires Loop ensures false;
          }
     }
{
  if (i < 0) return;
  else loop(i - j, j);
}
