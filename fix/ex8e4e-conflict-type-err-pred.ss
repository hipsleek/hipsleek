
data str {
  int val;
  str next;
}

data cell {
  int val;
}


EEE<> == self::cell<_>;

HHH<> == self::cell<_>
  or self::str<_,_> inv true;


/*
# ex8e4e.ss

# Fixed with a better error message ..

ERROR: at _0:0_0:0
Message: type conflict between 'cell' and 'str'

!!! **iast.ml#2168:XXX:view:HHH
!!! **iast.ml#2169:XXX:a:[str,cell]
!!! **iast.ml#2168:XXX:view:EEE
!!! **iast.ml#2169:XXX:a:[cell]

ERROR: at _0:0_0:0
Message: Can not find flow of str

ERROR: at ex8e4d-conflict-type-err-pred.ss_14:9_14:20
Message: gather_type_info_var : unexpected exception Failure("Can not find flow of str")

!!! **main.ml#1177:WARNING : Logging not done on finalize
Stop Omega... 0 invocations caught

Exception occurred: Failure("gather_type_info_var : unexpected exception Failure(\"Can not find flow of str\")")
Error3(s) detected at main 



*/


