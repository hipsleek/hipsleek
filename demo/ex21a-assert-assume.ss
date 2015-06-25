
void fc(int x)
 requires x<0 ensures true;

void foo(int x)
  requires true
  ensures true;
{
  if (x>0) {
    assert x'>=5 assume true;
    dprint;
    assert x'>=0;
    assert x'<0;
  }
}

/*
# ex21a

{
  if (x>0) {
    assert x'>=5 assume true;
    dprint;
    assert x'>=0;
    assert x'<0;
  }
}

incorrect to have false in post-state; do we
need to turn on a flag? it is incorrect!
Once assert/assume fail, the method should fail.

assert/assume:ex21a-assert-assume.ss:6: 4:  : failed


!!! **typechecker.ml#2010:Dprint:[x]
dprint(simpl): ex21a-assert-assume.ss:7: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:hfalse&false&{FLOW,(4,5)=__norm#E}[]

 ]


Procedure foo$int SUCCESS.



*/
