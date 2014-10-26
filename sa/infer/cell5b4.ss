data cell {
  int val;
}

void wloop(cell x,cell y)
    infer[@shape]
    requires true
    ensures true;
{
  wloop(x,y);
  dprint;
}

/*
# cell5b3.ss 

Expecting :
  HP(..) = true
  GP(..) = false

But currently has an error:

[ // PRE_REC
(0)HP_11(x@NI,y@NI)&true --> HP_11(x@NI,y@NI)&
true(4,5),
 // POST
(0)GP_12(x,y)&true --> GP_12(x,y)&
true(4,5)]

Procedure wloop$cell~cell SUCCESS.

!!! shape inference for flow:(4,5)
 --error:  at:(Program not linked with -g, cannot print stack backtrace)

*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[]
*************************************



*/
