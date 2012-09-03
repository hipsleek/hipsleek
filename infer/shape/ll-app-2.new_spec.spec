 append
 requires x::ll2<m,sm_562,lg_563> * y::ll2<n,sm_564,lg_565> & x!=null & 
lg_563<=sm_564 & true
 ensures x::ll2<z_682,sm_683,lg_684> & z_682=n+m & 
lg_563>=sm_683 & sm_564>=lg_563 & lg_684>=sm_564 & sm_683=sm_562 & 
lg_684=lg_565 & 0<=m & sm_562<=lg_563 & 0<=n & sm_564<=lg_565;