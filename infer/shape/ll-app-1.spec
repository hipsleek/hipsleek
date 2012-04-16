append
infer {ll->ll1} @xpost []
requires x::ll<>*y::ll<> & x!=null
ensures x::ll<>;
