void loop(int x, int z, int tx) 
/*
case {
  x < 0 | x > tx + z -> requires Term ensures true;
  x >= 0 & x <= tx + z -> case {
    z >= 0 -> requires Term[2,z] ensures true;
    z < 0 -> requires Term[1,x] ensures true;
  }
}
*/
{
  if (x >= 0 && x <= tx + z) {
    z = z - 1;
    tx = x;
    x = __VERIFIER_nondet_int();
    loop(x, z, tx);
  }
}
