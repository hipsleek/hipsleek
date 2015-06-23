relation R(int x).

int add1 (int x)
     infer [R]
     requires R(x)
     ensures true;
{
    return x + 1;
}

/*
# ex25.ss

No output / nothing to infer with no recursive call.
a trace `-dre analyse` (fn which analyses the params)
shows empty infer_rel given

 */
