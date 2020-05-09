//Ex.1: array inside a struct

typedef struct _overflow {
  int a[9];
  double c;
} overflow;

/*@
pred buf<arr, d> == self::_overflow<arr, c> & dom(arr, 0, 8);
*/

overflow* malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::buf<a, c>;
  }
*/;

int main()
{
  overflow* s = malloc(sizeof(overflow));

  int i = 8;
  s->a[i] = 0; //buffer-overflow 1
  s->a[i+1] = 0; //buffer-overflow 2
  s->c = 2.0;
  free(s);
  return 0;
}
