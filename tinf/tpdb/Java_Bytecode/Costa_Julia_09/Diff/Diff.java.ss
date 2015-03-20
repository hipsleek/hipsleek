

data Diff
{

}
 void Diff_dif(int[] A, int[] B, int[] D)
{
  int k = 0;
  int i = 0;
  int l1 = A.length;
  int l2 = B.length;
  boolean found;
  while (i < l1) {
    int j = 0;
    found = false;
    while (j < l2 && !found) {
      if (A[i] == B[j])
        found = true;
      else
        j++;
    }
    if (!found) {
      D[k] = A[i];
      k++;
    }
    i++;
  }
}

void Diff_main(String[] args)
{
  Diff_dif(new int[20], new int[20], new int[20]);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;