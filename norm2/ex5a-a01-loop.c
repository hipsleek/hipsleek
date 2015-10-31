int test_fun (int* x_ref, int* y_ref, int* c)
/*@
  infer[@shape_prepost,@term]
  requires true
  ensures true;
*/
{
    while (*y_ref < *x_ref) 
      /*@
        infer[@shape_prepost,@term]
        requires true
        ensures true;
      */
      {
            *y_ref = *y_ref + 1;
            *c = *c + 1;
      }
    return *c;
}

int main() {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
