
global int TriTas_N;

global int[] TriTas_a;

global int TriTas_nTas = 0;
data TriTas
{

}
 void TriTas_Ajouter(int v)
{
  int i;
  int j;
  TriTas_nTas++;
  i = TriTas_nTas - 1;
  while (i > 0 && TriTas_a[(i - 1) / 2] <= v) {
    TriTas_a[i] = TriTas_a[(i - 1) / 2];
    j = (i - 1) / 2;
    if (j >= i)
      break;
    else
      i = j;
  }
  TriTas_a[i] = v;
}

int TriTas_Maximum()
{
  return TriTas_a[0];
}

void TriTas_Supprimer()
{
  int i;
  int j;
  int v;
  TriTas_a[0] = TriTas_a[TriTas_nTas - 1];
  TriTas_nTas--;
  i = 0;
  v = TriTas_a[0];
  while (2 * i + 1 < TriTas_nTas) {
    j = 2 * i + 1;
    if (j + 1 < TriTas_nTas)
      if (TriTas_a[j + 1] > TriTas_a[j])
        j++;
    if (v >= TriTas_a[j])
      break;
    TriTas_a[i] = TriTas_a[j];
    i = j;
  }
  TriTas_a[i] = v;
}

void TriTas_HeapSort()
{
