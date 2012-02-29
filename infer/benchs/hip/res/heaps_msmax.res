
Processing file "heaps_msmax.ss"
Parsing heaps_msmax.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure ripple$int~int~int~int~node~node... 
Procedure ripple$int~int~int~int~node~node SUCCESS

Checking procedure deletemax$node... 
!!! REL :  DELM(mx,mx2,res)
!!! POST:  mx2>=0 & res>=mx2 & mx>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DELM]
              EBase exists (Expl)(Impl)[n; 
                    mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{325}]&(
                    ([0!=n & 0<=n][0<=mx][null!=t]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                EXISTS(flted_206_53,
                                mx2: t'::pq<flted_206_53,mx2>@M[Orig][LHSCase]@ rem br[{326,325}]&
                                (
                                ([0<=flted_206_53 & 1+flted_206_53=n]
                                 [0<=mx2 & DELM(mx,mx2,res)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{325}]&(
                  ([1<=n][0<=mx][t!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              EXISTS(flted_206_3352,
                              mx2_3353: t'::pq<flted_206_3352,mx2_3353>@M[Orig][LHSCase]@ rem br[{326,325}]&
                              (
                              ([res<=mx & 0<=mx & 0<=mx2_3353 & mx2_3353<=res]
                               [0<=flted_206_3352 & 0<=n & 1+flted_206_3352=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(maxi_2114:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=maxi_2114 & 
  maxi_2114<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2169:exists(max1_2436:exists(mx1_2099:exists(mx1_1937:exists(max2_2437:exists(v_54':res<=mx & 
  exists(maxi_2171:exists(tval_2440:maxi_2171<=res & 
  exists(mx3_2438:exists(mx4_2170:mx3_2438<=tval_2440 & 0<=mx3_2438 & 
  exists(mx4_2439:(mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx4_2170=max2_2437 & mx3_2169=mx1_2099 & max1_2436=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_2438<=mx1_2099 & mx1_2099<=max2_2437 & 
  max2_2437<=mx2 & mx2<=maxi_2171 & tval_2440<=max2_2437 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx3_2169=mx1_2099 & 
  max1_2436=max2_2437 & v_54'=max2_2437 & tval_2440<=max2_2437 & (1+
  mx1_2099)<=max2_2437 & (1+mx4_2170)<=max2_2437 & max2_2437<=mx2 & 
  mx3_2438<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2439<=mx4_2170 | mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx3_2169=mx1_2099 & max1_2436=max2_2437 & v_54'=max2_2437 & (1+
  mx1_2099)<=max2_2437 & (1+mx4_2170)<=max2_2437 & tval_2440<=max2_2437 & 
  max2_2437<=maxi_2171 & mx4_2439<=mx4_2170 & mx4_2170<=mx2 & 
  mx2<=maxi_2171 & tval_2440<=mx2 & mx3_2438<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2171=mx2 & mx1=mx1_1937 & max2_2437=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2436=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2440<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2439<=mx4_2170 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2171 & 
  mx1=maxi_2171 & max2_2437=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2436=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2440<=mx1_2099 & mx1_2099<=maxi_2171 & mx4_2439<=mx4_2170 & 
  mx4_2170<=mx2 & mx2<=maxi_2171 & tval_2440<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx4_2170=max2_2437 & 
  mx3_2169=mx1_2099 & v_54'=max1_2436 & mx3_2438<=mx1_2099 & (1+
  mx1_2099)<=max1_2436 & max1_2436<=max2_2437 & max2_2437<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_2440<=max2_2437 | 
  mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & mx4_2170=max2_2437 & 
  mx3_2169=mx1_2099 & v_54'=max1_2436 & mx3_2438<=mx1_2099 & (1+
  mx1_2099)<=max1_2436 & max1_2436<=max2_2437 & max2_2437<=mx2 & 
  mx2<=maxi_2171 & tval_2440<=max2_2437 | mx2_1940=mx2 & maxi_2171=mx2 & 
  mx1=mx1_1937 & mx4_2170=max2_2437 & mx3_2169=mx1_2099 & 
  max1_2436=mx1_2099 & v_54'<=mx1_2099 & mx3_2438<=mx1_2099 & 
  mx1_2099<=max2_2437 & max2_2437<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_2440<=max2_2437 & 0<=v_54') & mx4_2439<=tval_2440 & 
  0<=mx4_2439)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2169:exists(max1_2533:exists(mx1_2099:exists(mx1_1937:exists(max2_2534:exists(v_54':res<=mx & 
  exists(maxi_2171:exists(tval_2537:maxi_2171<=res & 
  exists(mx3_2535:exists(mx4_2170:mx3_2535<=tval_2537 & 0<=mx3_2535 & 
  exists(mx4_2536:(mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx4_2170=max2_2534 & mx3_2169=mx1_2099 & max1_2533=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_2535<=mx1_2099 & mx1_2099<=max2_2534 & 
  max2_2534<=mx2 & mx2<=maxi_2171 & tval_2537<=max2_2534 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx3_2169=mx1_2099 & 
  max1_2533=max2_2534 & v_54'=max2_2534 & tval_2537<=max2_2534 & (1+
  mx1_2099)<=max2_2534 & (1+mx4_2170)<=max2_2534 & max2_2534<=mx2 & 
  mx3_2535<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2536<=mx4_2170 | mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx3_2169=mx1_2099 & max1_2533=max2_2534 & v_54'=max2_2534 & (1+
  mx1_2099)<=max2_2534 & (1+mx4_2170)<=max2_2534 & tval_2537<=max2_2534 & 
  max2_2534<=maxi_2171 & mx4_2536<=mx4_2170 & mx4_2170<=mx2 & 
  mx2<=maxi_2171 & tval_2537<=mx2 & mx3_2535<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2171=mx2 & mx1=mx1_1937 & max2_2534=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2533=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2537<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2536<=mx4_2170 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2171 & 
  mx1=maxi_2171 & max2_2534=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2533=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2537<=mx1_2099 & mx1_2099<=maxi_2171 & mx4_2536<=mx4_2170 & 
  mx4_2170<=mx2 & mx2<=maxi_2171 & tval_2537<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx4_2170=max2_2534 & 
  mx3_2169=mx1_2099 & v_54'=max1_2533 & mx3_2535<=mx1_2099 & (1+
  mx1_2099)<=max1_2533 & max1_2533<=max2_2534 & max2_2534<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_2537<=max2_2534 | 
  mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & mx4_2170=max2_2534 & 
  mx3_2169=mx1_2099 & v_54'=max1_2533 & mx3_2535<=mx1_2099 & (1+
  mx1_2099)<=max1_2533 & max1_2533<=max2_2534 & max2_2534<=mx2 & 
  mx2<=maxi_2171 & tval_2537<=max2_2534 | mx2_1940=mx2 & maxi_2171=mx2 & 
  mx1=mx1_1937 & mx4_2170=max2_2534 & mx3_2169=mx1_2099 & 
  max1_2533=mx1_2099 & v_54'<=mx1_2099 & mx3_2535<=mx1_2099 & 
  mx1_2099<=max2_2534 & max2_2534<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_2537<=max2_2534 & 0<=v_54') & mx4_2536<=tval_2537 & 
  0<=mx4_2536)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2169:exists(max1_2630:exists(mx1_2099:exists(mx1_1937:exists(max2_2631:exists(v_54':res<=mx & 
  exists(maxi_2171:exists(tval_2634:maxi_2171<=res & 
  exists(mx3_2632:exists(mx4_2170:mx3_2632<=tval_2634 & 0<=mx3_2632 & 
  exists(mx4_2633:(mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx4_2170=max2_2631 & mx3_2169=mx1_2099 & max1_2630=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_2632<=mx1_2099 & mx1_2099<=max2_2631 & 
  max2_2631<=mx2 & mx2<=maxi_2171 & tval_2634<=max2_2631 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx3_2169=mx1_2099 & 
  max1_2630=max2_2631 & v_54'=max2_2631 & tval_2634<=max2_2631 & (1+
  mx1_2099)<=max2_2631 & (1+mx4_2170)<=max2_2631 & max2_2631<=mx2 & 
  mx3_2632<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2633<=mx4_2170 | mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx3_2169=mx1_2099 & max1_2630=max2_2631 & v_54'=max2_2631 & (1+
  mx1_2099)<=max2_2631 & (1+mx4_2170)<=max2_2631 & tval_2634<=max2_2631 & 
  max2_2631<=maxi_2171 & mx4_2633<=mx4_2170 & mx4_2170<=mx2 & 
  mx2<=maxi_2171 & tval_2634<=mx2 & mx3_2632<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2171=mx2 & mx1=mx1_1937 & max2_2631=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2630=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2634<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2633<=mx4_2170 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2171 & 
  mx1=maxi_2171 & max2_2631=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2630=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2634<=mx1_2099 & mx1_2099<=maxi_2171 & mx4_2633<=mx4_2170 & 
  mx4_2170<=mx2 & mx2<=maxi_2171 & tval_2634<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx4_2170=max2_2631 & 
  mx3_2169=mx1_2099 & v_54'=max1_2630 & mx3_2632<=mx1_2099 & (1+
  mx1_2099)<=max1_2630 & max1_2630<=max2_2631 & max2_2631<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_2634<=max2_2631 | 
  mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & mx4_2170=max2_2631 & 
  mx3_2169=mx1_2099 & v_54'=max1_2630 & mx3_2632<=mx1_2099 & (1+
  mx1_2099)<=max1_2630 & max1_2630<=max2_2631 & max2_2631<=mx2 & 
  mx2<=maxi_2171 & tval_2634<=max2_2631 | mx2_1940=mx2 & maxi_2171=mx2 & 
  mx1=mx1_1937 & mx4_2170=max2_2631 & mx3_2169=mx1_2099 & 
  max1_2630=mx1_2099 & v_54'<=mx1_2099 & mx3_2632<=mx1_2099 & 
  mx1_2099<=max2_2631 & max2_2631<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_2634<=max2_2631 & 0<=v_54') & mx4_2633<=tval_2634 & 
  0<=mx4_2633)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2169:exists(max1_2783:exists(mx1_2099:exists(mx1_1937:exists(max2_2784:exists(v_54':res<=mx & 
  exists(maxi_2171:exists(tval_2787:maxi_2171<=res & 
  exists(mx3_2785:exists(mx4_2170:mx3_2785<=tval_2787 & 0<=mx3_2785 & 
  exists(mx4_2786:(mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx4_2170=max2_2784 & mx3_2169=mx1_2099 & max1_2783=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_2785<=mx1_2099 & mx1_2099<=max2_2784 & 
  max2_2784<=mx2 & mx2<=maxi_2171 & tval_2787<=max2_2784 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx3_2169=mx1_2099 & 
  max1_2783=max2_2784 & v_54'=max2_2784 & tval_2787<=max2_2784 & (1+
  mx1_2099)<=max2_2784 & (1+mx4_2170)<=max2_2784 & max2_2784<=mx2 & 
  mx3_2785<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2786<=mx4_2170 | mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & 
  mx3_2169=mx1_2099 & max1_2783=max2_2784 & v_54'=max2_2784 & (1+
  mx1_2099)<=max2_2784 & (1+mx4_2170)<=max2_2784 & tval_2787<=max2_2784 & 
  max2_2784<=maxi_2171 & mx4_2786<=mx4_2170 & mx4_2170<=mx2 & 
  mx2<=maxi_2171 & tval_2787<=mx2 & mx3_2785<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2171=mx2 & mx1=mx1_1937 & max2_2784=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2783=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2787<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2786<=mx4_2170 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2171 & 
  mx1=maxi_2171 & max2_2784=mx1_2099 & mx3_2169=mx1_2099 & 
  max1_2783=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2170)<=mx1_2099 & 
  tval_2787<=mx1_2099 & mx1_2099<=maxi_2171 & mx4_2786<=mx4_2170 & 
  mx4_2170<=mx2 & mx2<=maxi_2171 & tval_2787<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2171=mx2 & mx1=mx1_1937 & mx4_2170=max2_2784 & 
  mx3_2169=mx1_2099 & v_54'=max1_2783 & mx3_2785<=mx1_2099 & (1+
  mx1_2099)<=max1_2783 & max1_2783<=max2_2784 & max2_2784<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_2787<=max2_2784 | 
  mx2_1940=mx2 & mx1_1937=maxi_2171 & mx1=maxi_2171 & mx4_2170=max2_2784 & 
  mx3_2169=mx1_2099 & v_54'=max1_2783 & mx3_2785<=mx1_2099 & (1+
  mx1_2099)<=max1_2783 & max1_2783<=max2_2784 & max2_2784<=mx2 & 
  mx2<=maxi_2171 & tval_2787<=max2_2784 | mx2_1940=mx2 & maxi_2171=mx2 & 
  mx1=mx1_1937 & mx4_2170=max2_2784 & mx3_2169=mx1_2099 & 
  max1_2783=mx1_2099 & v_54'<=mx1_2099 & mx3_2785<=mx1_2099 & 
  mx1_2099<=max2_2784 & max2_2784<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_2787<=max2_2784 & 0<=v_54') & mx4_2786<=tval_2787 & 
  0<=mx4_2786)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(maxi_2194:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=maxi_2194 & 
  maxi_2194<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2249:exists(max1_2862:exists(mx1_2099:exists(mx1_1937:exists(max2_2863:exists(v_54':res<=mx & 
  exists(maxi_2251:exists(tval_2866:maxi_2251<=res & 
  exists(mx3_2864:exists(mx4_2250:mx3_2864<=tval_2866 & 0<=mx3_2864 & 
  exists(mx4_2865:(mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx4_2250=max2_2863 & mx3_2249=mx1_2099 & max1_2862=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_2864<=mx1_2099 & mx1_2099<=max2_2863 & 
  max2_2863<=mx2 & mx2<=maxi_2251 & tval_2866<=max2_2863 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx3_2249=mx1_2099 & 
  max1_2862=max2_2863 & v_54'=max2_2863 & tval_2866<=max2_2863 & (1+
  mx1_2099)<=max2_2863 & (1+mx4_2250)<=max2_2863 & max2_2863<=mx2 & 
  mx3_2864<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2865<=mx4_2250 | mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx3_2249=mx1_2099 & max1_2862=max2_2863 & v_54'=max2_2863 & (1+
  mx1_2099)<=max2_2863 & (1+mx4_2250)<=max2_2863 & tval_2866<=max2_2863 & 
  max2_2863<=maxi_2251 & mx4_2865<=mx4_2250 & mx4_2250<=mx2 & 
  mx2<=maxi_2251 & tval_2866<=mx2 & mx3_2864<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2251=mx2 & mx1=mx1_1937 & max2_2863=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_2862=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_2866<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2865<=mx4_2250 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2251 & 
  mx1=maxi_2251 & max2_2863=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_2862=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_2866<=mx1_2099 & mx1_2099<=maxi_2251 & mx4_2865<=mx4_2250 & 
  mx4_2250<=mx2 & mx2<=maxi_2251 & tval_2866<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx4_2250=max2_2863 & 
  mx3_2249=mx1_2099 & v_54'=max1_2862 & mx3_2864<=mx1_2099 & (1+
  mx1_2099)<=max1_2862 & max1_2862<=max2_2863 & max2_2863<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_2866<=max2_2863 | 
  mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & mx4_2250=max2_2863 & 
  mx3_2249=mx1_2099 & v_54'=max1_2862 & mx3_2864<=mx1_2099 & (1+
  mx1_2099)<=max1_2862 & max1_2862<=max2_2863 & max2_2863<=mx2 & 
  mx2<=maxi_2251 & tval_2866<=max2_2863 | mx2_1940=mx2 & maxi_2251=mx2 & 
  mx1=mx1_1937 & mx4_2250=max2_2863 & mx3_2249=mx1_2099 & 
  max1_2862=mx1_2099 & v_54'<=mx1_2099 & mx3_2864<=mx1_2099 & 
  mx1_2099<=max2_2863 & max2_2863<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_2866<=max2_2863 & 0<=v_54') & mx4_2865<=tval_2866 & 
  0<=mx4_2865)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1_1937:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1_1937 & 
  mx1_1937<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2249:exists(max1_2961:exists(mx1_2099:exists(mx1_1937:exists(max2_2962:exists(v_54':res<=mx & 
  exists(maxi_2251:exists(tval_2965:maxi_2251<=res & 
  exists(mx3_2963:exists(mx4_2250:mx3_2963<=tval_2965 & 0<=mx3_2963 & 
  exists(mx4_2964:(mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx4_2250=max2_2962 & mx3_2249=mx1_2099 & max1_2961=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_2963<=mx1_2099 & mx1_2099<=max2_2962 & 
  max2_2962<=mx2 & mx2<=maxi_2251 & tval_2965<=max2_2962 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx3_2249=mx1_2099 & 
  max1_2961=max2_2962 & v_54'=max2_2962 & tval_2965<=max2_2962 & (1+
  mx1_2099)<=max2_2962 & (1+mx4_2250)<=max2_2962 & max2_2962<=mx2 & 
  mx3_2963<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2964<=mx4_2250 | mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx3_2249=mx1_2099 & max1_2961=max2_2962 & v_54'=max2_2962 & (1+
  mx1_2099)<=max2_2962 & (1+mx4_2250)<=max2_2962 & tval_2965<=max2_2962 & 
  max2_2962<=maxi_2251 & mx4_2964<=mx4_2250 & mx4_2250<=mx2 & 
  mx2<=maxi_2251 & tval_2965<=mx2 & mx3_2963<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2251=mx2 & mx1=mx1_1937 & max2_2962=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_2961=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_2965<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_2964<=mx4_2250 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2251 & 
  mx1=maxi_2251 & max2_2962=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_2961=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_2965<=mx1_2099 & mx1_2099<=maxi_2251 & mx4_2964<=mx4_2250 & 
  mx4_2250<=mx2 & mx2<=maxi_2251 & tval_2965<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx4_2250=max2_2962 & 
  mx3_2249=mx1_2099 & v_54'=max1_2961 & mx3_2963<=mx1_2099 & (1+
  mx1_2099)<=max1_2961 & max1_2961<=max2_2962 & max2_2962<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_2965<=max2_2962 | 
  mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & mx4_2250=max2_2962 & 
  mx3_2249=mx1_2099 & v_54'=max1_2961 & mx3_2963<=mx1_2099 & (1+
  mx1_2099)<=max1_2961 & max1_2961<=max2_2962 & max2_2962<=mx2 & 
  mx2<=maxi_2251 & tval_2965<=max2_2962 | mx2_1940=mx2 & maxi_2251=mx2 & 
  mx1=mx1_1937 & mx4_2250=max2_2962 & mx3_2249=mx1_2099 & 
  max1_2961=mx1_2099 & v_54'<=mx1_2099 & mx3_2963<=mx1_2099 & 
  mx1_2099<=max2_2962 & max2_2962<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_2965<=max2_2962 & 0<=v_54') & mx4_2964<=tval_2965 & 
  0<=mx4_2964)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1_1937:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1_1937 & 
  mx1_1937<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1_1937:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1_1937 & 
  mx1_1937<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2249:exists(max1_3060:exists(mx1_2099:exists(mx1_1937:exists(max2_3061:exists(v_54':res<=mx & 
  exists(maxi_2251:exists(tval_3064:maxi_2251<=res & 
  exists(mx3_3062:exists(mx4_2250:mx3_3062<=tval_3064 & 0<=mx3_3062 & 
  exists(mx4_3063:(mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx4_2250=max2_3061 & mx3_2249=mx1_2099 & max1_3060=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_3062<=mx1_2099 & mx1_2099<=max2_3061 & 
  max2_3061<=mx2 & mx2<=maxi_2251 & tval_3064<=max2_3061 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx3_2249=mx1_2099 & 
  max1_3060=max2_3061 & v_54'=max2_3061 & tval_3064<=max2_3061 & (1+
  mx1_2099)<=max2_3061 & (1+mx4_2250)<=max2_3061 & max2_3061<=mx2 & 
  mx3_3062<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_3063<=mx4_2250 | mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx3_2249=mx1_2099 & max1_3060=max2_3061 & v_54'=max2_3061 & (1+
  mx1_2099)<=max2_3061 & (1+mx4_2250)<=max2_3061 & tval_3064<=max2_3061 & 
  max2_3061<=maxi_2251 & mx4_3063<=mx4_2250 & mx4_2250<=mx2 & 
  mx2<=maxi_2251 & tval_3064<=mx2 & mx3_3062<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2251=mx2 & mx1=mx1_1937 & max2_3061=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_3060=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_3064<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_3063<=mx4_2250 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2251 & 
  mx1=maxi_2251 & max2_3061=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_3060=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_3064<=mx1_2099 & mx1_2099<=maxi_2251 & mx4_3063<=mx4_2250 & 
  mx4_2250<=mx2 & mx2<=maxi_2251 & tval_3064<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx4_2250=max2_3061 & 
  mx3_2249=mx1_2099 & v_54'=max1_3060 & mx3_3062<=mx1_2099 & (1+
  mx1_2099)<=max1_3060 & max1_3060<=max2_3061 & max2_3061<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_3064<=max2_3061 | 
  mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & mx4_2250=max2_3061 & 
  mx3_2249=mx1_2099 & v_54'=max1_3060 & mx3_3062<=mx1_2099 & (1+
  mx1_2099)<=max1_3060 & max1_3060<=max2_3061 & max2_3061<=mx2 & 
  mx2<=maxi_2251 & tval_3064<=max2_3061 | mx2_1940=mx2 & maxi_2251=mx2 & 
  mx1=mx1_1937 & mx4_2250=max2_3061 & mx3_2249=mx1_2099 & 
  max1_3060=mx1_2099 & v_54'<=mx1_2099 & mx3_3062<=mx1_2099 & 
  mx1_2099<=max2_3061 & max2_3061<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_3064<=max2_3061 & 0<=v_54') & mx4_3063<=tval_3064 & 
  0<=mx4_3063)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(maxi_2194:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=maxi_2194 & 
  maxi_2194<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(maxi_2194:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=maxi_2194 & 
  maxi_2194<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1_1937:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1_1937 & 
  mx1_1937<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (mx2=0 & 0<=res & res<=mx) --> DELM(mx,mx2,res),
 (exists(v_int_224_617':exists(d_1934:mx2=0 & exists(mx1:res<=mx & 
  v_int_224_617'=res & d_1934=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1940:exists(mx1:exists(mx3_2249:exists(max1_3315:exists(mx1_2099:exists(mx1_1937:exists(max2_3316:exists(v_54':res<=mx & 
  exists(maxi_2251:exists(tval_3319:maxi_2251<=res & 
  exists(mx3_3317:exists(mx4_2250:mx3_3317<=tval_3319 & 0<=mx3_3317 & 
  exists(mx4_3318:(mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx4_2250=max2_3316 & mx3_2249=mx1_2099 & max1_3315=mx1_2099 & 
  v_54'<=mx1_2099 & mx3_3317<=mx1_2099 & mx1_2099<=max2_3316 & 
  max2_3316<=mx2 & mx2<=maxi_2251 & tval_3319<=max2_3316 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx3_2249=mx1_2099 & 
  max1_3315=max2_3316 & v_54'=max2_3316 & tval_3319<=max2_3316 & (1+
  mx1_2099)<=max2_3316 & (1+mx4_2250)<=max2_3316 & max2_3316<=mx2 & 
  mx3_3317<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_3318<=mx4_2250 | mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & 
  mx3_2249=mx1_2099 & max1_3315=max2_3316 & v_54'=max2_3316 & (1+
  mx1_2099)<=max2_3316 & (1+mx4_2250)<=max2_3316 & tval_3319<=max2_3316 & 
  max2_3316<=maxi_2251 & mx4_3318<=mx4_2250 & mx4_2250<=mx2 & 
  mx2<=maxi_2251 & tval_3319<=mx2 & mx3_3317<=mx1_2099 | mx2_1940=mx2 & 
  maxi_2251=mx2 & mx1=mx1_1937 & max2_3316=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_3315=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_3319<=mx1_2099 & mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & 
  mx4_3318<=mx4_2250 & 0<=v_54' | mx2_1940=mx2 & mx1_1937=maxi_2251 & 
  mx1=maxi_2251 & max2_3316=mx1_2099 & mx3_2249=mx1_2099 & 
  max1_3315=mx1_2099 & v_54'<=mx1_2099 & (1+mx4_2250)<=mx1_2099 & 
  tval_3319<=mx1_2099 & mx1_2099<=maxi_2251 & mx4_3318<=mx4_2250 & 
  mx4_2250<=mx2 & mx2<=maxi_2251 & tval_3319<=mx2 & 0<=v_54' | 
  mx2_1940=mx2 & maxi_2251=mx2 & mx1=mx1_1937 & mx4_2250=max2_3316 & 
  mx3_2249=mx1_2099 & v_54'=max1_3315 & mx3_3317<=mx1_2099 & (1+
  mx1_2099)<=max1_3315 & max1_3315<=max2_3316 & max2_3316<=mx2 & 
  mx1_2099<=mx1_1937 & (1+mx1_1937)<=mx2 & tval_3319<=max2_3316 | 
  mx2_1940=mx2 & mx1_1937=maxi_2251 & mx1=maxi_2251 & mx4_2250=max2_3316 & 
  mx3_2249=mx1_2099 & v_54'=max1_3315 & mx3_3317<=mx1_2099 & (1+
  mx1_2099)<=max1_3315 & max1_3315<=max2_3316 & max2_3316<=mx2 & 
  mx2<=maxi_2251 & tval_3319<=max2_3316 | mx2_1940=mx2 & maxi_2251=mx2 & 
  mx1=mx1_1937 & mx4_2250=max2_3316 & mx3_2249=mx1_2099 & 
  max1_3315=mx1_2099 & v_54'<=mx1_2099 & mx3_3317<=mx1_2099 & 
  mx1_2099<=max2_3316 & max2_3316<=mx2 & mx1_2099<=mx1_1937 & (1+
  mx1_1937)<=mx2 & tval_3319<=max2_3316 & 0<=v_54') & mx4_3318<=tval_3319 & 
  0<=mx4_3318)))))))))))))) --> DELM(mx,mx2,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
Procedure deleteoneel$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 3244 invocations 
1 false contexts at: ( (156,2) )

Total verification time: 18.21 second(s)
	Time spent in main process: 10.62 second(s)
	Time spent in child processes: 7.59 second(s)
