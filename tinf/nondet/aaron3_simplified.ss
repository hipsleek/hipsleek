void loop(int x, int z, int tx) 

{
  if (x >= 0 && x <= tx + z) {
    z = z - 1;
    tx = x;
    x = __VERIFIER_nondet_int();
    loop(x, z, tx);
  }
}
