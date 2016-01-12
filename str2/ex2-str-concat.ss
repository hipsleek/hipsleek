checksat x="se"@y@"st"@z.
expect Valid.

checkentail res=x@x |- res=x@y.
expect Fail.

checkentail res=x@x & x=y |- res=x@y.
expect Valiod.


