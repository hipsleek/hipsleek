extern int __VERIFIER_nondet_int(void);

void bubbleSort(int numbers[], int array_size)
/*@
  requires numbers::Aseg<0, array_size> & array_size > 0
  ensures numbers::Aseg<0, array_size>;
*/
{
    int i, j, temp;
     
    for (i = (array_size - 1); i >= 0; i--)
      /*@
	case{
	i>=0 -> 
	requires numbers::Aseg<0, i+1> & i>=0 & i<array_size
	ensures numbers::Aseg<0, i+1>;
	i<0 ->
	requires emp & i=-1
	ensures emp;
	}
      */
      {
        for (j = 1; j <= i; j++)
	  /*@
	    case{
	    j<=i ->
	    requires numbers::AsegNE<j-1, i+1> & j>=1 & j<=i & i>=1 
	    ensures numbers::AsegNE<j-1, i+1>;
	    j>i ->
	    requires emp & j>=1
	    ensures emp;
	    }
	  */
	  {
            if (numbers[j-1] > numbers[j]) {
                temp = numbers[j-1];
                numbers[j-1] = numbers[j];
                numbers[j] = temp;
            }
        }
    }
}

int main() {
  int* numbers;
  int array_size = __VERIFIER_nondet_int();
  bubbleSort(numbers, array_size);
  return 0;
}
