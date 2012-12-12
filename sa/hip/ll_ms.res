Starting Omega...oc
Translating global variables to procedure parameters...
gather_type_info_b_formula: relation SIZEH

Checking procedure create_list$int~int... 
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 187::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]&
                                CL(m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 187::
                      EXISTS(m: res::ll<m>@M[Orig][LHSCase]&m>=0 & m=n&
                      {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=0 & m=0) --> CL(m,n),
 ((n=n'+1 & m=m_1020+1 & 0<=m_1020 & 0<=n' | n=n'+1 & m=m_1020+1 & n'<=(0-
  2) & 0<=m_1020) & CL(m_1020,n')) --> CL(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: 
  Some(emp&x'=null & n=0 & x'=x & a'=a & a'=1 & v_bool_285_839' & a'=a' & 
  v_bool_285_839'&{FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [n; a]
 es_infer_vars_rel: [DEL]
 es_var_zero_perm: 

!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: 
  Some(x'::node<Anon_1054,q_1055>@M[Orig]&v_node_286_828'=null & 
  flted_11_1053=0 & flted_11_1053+1=n & x'=x & a'=a & a'=1 & 
  v_bool_285_839' & a'=a' & v_bool_285_839' & v_node_286_828'=q_1055&
  {FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [n; a]
 es_infer_vars_rel: [DEL]
 es_infer_pure: [n!=0 | a!=1]
 es_var_zero_perm: 

!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: 
  Some(emp&x'=null & n=0 & x'=x & a'=a & a'!=1 & !(v_bool_285_839') & 
  a'!=1 & !(v_bool_285_839')&{FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [n; a]
 es_infer_vars_rel: [DEL]
 es_var_zero_perm: 

!!! OLD SPECS: ((None,[]),EInfer [n,a,DEL]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 180::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&
                                DEL(m,n,a)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&1<=a & a<n & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 180::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&a>=1 & 
                              m>=a & m+1=n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (a=1 & m=n-1 & 2<=n) --> DEL(m,n,a),
 ((n_1106=n-1 & v_int_289_1124=a-1 & m=m_1123+1 & 1<=n & 0<=m_1123 & 2<=a | 
  n_1106=n-1 & v_int_289_1124=a-1 & m=m_1123+1 & a<=0 & 1<=n & 0<=m_1123) & 
  DEL(m_1123,n_1106,v_int_289_1124)) --> DEL(m,n,a)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 184::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]&
                                DEL2(m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 184::
                              EXISTS(m: res::ll<m>@M[Orig][LHSCase]&(m+
                              1)>=n & m>=0 & n>=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=0 & m=0) --> DEL2(m,n),
 (m=n-1 & 1<=n) --> DEL2(m,n),
 (n_1177=n-1 & m=m_1192+1 & 1<=n & 0<=m_1192 & 
  DEL2(m_1192,n_1177)) --> DEL2(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_1211]
!!! es_infer_vars_hp_rel: [H,G,HP_1211]
!!! es_infer_vars_hp_rel: [H,G]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 151::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 151::ref [x]
                              
                              EXISTS(G: htrue * G(x,x')&x'=null & x!=null&
                              {FLOW,(22,23)=__norm})[]
                              or EXISTS(G: htrue * G(x,x')&x=x' & x'=null&
                                 {FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&x!=null&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_34_952',next_34_953'>@L[Orig] * 
  HP_1211(next_34_953',x)&true&{FLOW,(1,25)=__flow}[],
 (HP_1211(v_node_34_954',x) * x::node<val_34_1218,v_node_34_954'>@M[Orig]&
  x!=null&{FLOW,(22,23)=__norm}[]) --> H(v_node_34_954')&true&
  {FLOW,(22,23)=__norm}[],
 (emp&x'=null & x!=null&{FLOW,(22,23)=__norm}[]) --> G(x,x')&true&
  {FLOW,(22,23)=__norm}[],
 (H(x)&x=null&{FLOW,(22,23)=__norm}[]) --> G(x,x)&true&
  {FLOW,(22,23)=__norm}[]]
Procedure delete_list$node SUCCESS

Checking procedure find_ge$node~int... 
!!! es_infer_vars_hp_rel: []
!!! es_infer_vars_hp_rel: []
!!! es_infer_vars_hp_rel: []
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 230::
                                
                                emp&res=null&{FLOW,(22,23)=__norm}[]
                                or EXISTS(Anon_24,
                                   m: res::node<m,Anon_24>@M[Orig]&FGE(m,v)&
                                   {FLOW,(22,23)=__norm})[]
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 230::
                              
                              emp&res=null&{FLOW,(22,23)=__norm}[]
                              or EXISTS(Anon_24,
                                 m: res::node<m,Anon_24>@M[Orig]&m>=(1+v)&
                                 {FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[ (v<m) --> FGE(m,v),
 (m=m_1279 & v=v' & FGE(m_1279,v')) --> FGE(m,v)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure find_ge$node~int SUCCESS

Checking procedure get_next$node... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_1285]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 166::
                                G(x,res)&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 166::
                              EXISTS(x',val_214_1294,
                              G: x'::node<val_214_1294,next_215_914'>@M[Orig] * 
                              G(x,res)&x'=x & next_215_914'=null&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&true&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_214_910',next_214_911'>@L[Orig] * 
  HP_1285(next_214_911',x)&true&{FLOW,(1,25)=__flow}[],
 (HP_1285(v_node_216_915',x) * x::node<val_214_1294,next_215_914'>@M[Orig]&
  true&{FLOW,(22,23)=__norm}[]) --> G(x,v_node_216_915')&true&
  {FLOW,(22,23)=__norm}[]]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: 
  Some(x'::node<Anon_1311,q_1312>@M[Orig]&v_node_261_865'=null & 
  flted_11_1310=0 & flted_11_1310+1=n & x'=x & x!=null & 
  v_node_261_865'=q_1312&{FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [n]
 es_infer_vars_rel: [GNN]
 es_var_zero_perm: 

!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&
                    x!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 176::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]&
                                GNN(m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&2<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 176::
                              EXISTS(m: res::ll<m>@M[Orig][LHSCase]&m>=0 & m+
                              2=n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=n-2 & 2<=n) --> GNN(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&
                    x!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 177::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&INS(m,n)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 177::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&n>=1 & n+
                              1=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=1 & m=2) --> INS(m,n),
 (m_1391=m-1 & n=n_1368+1 & 2<=m & 0<=n_1368 & 
  INS(m_1391,n_1368)) --> INS(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! es_infer_vars_hp_rel: []
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 208::
                                EXISTS(n_41,
                                m: x::ll<n_41>@M[Orig][LHSCase] * 
                                res::ll<m>@M[Orig][LHSCase]&CPY(m,n) & 
                                n_41=n&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 208::
                              EXISTS(n_41,m: x::ll<n_41>@M[Orig][LHSCase] * 
                              res::ll<m>@M[Orig][LHSCase]&n_41=n & m>=0 & 
                              m=n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n_1425=n-1 & m=m_1436+1 & 0<=m_1436 & 1<=n & 
  CPY(m_1436,n_1425)) --> CPY(m,n),
 (n=0 & m=0) --> CPY(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 222::ref [x]
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]&
                                FIL(m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 222::ref [x]
                              EXISTS(m: res::ll<m>@M[Orig][LHSCase]&m>=0 & 
                              n>=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n_1504=n-1 & m_1537=m & 1<=n & 0<=m & FIL(m_1537,n_1504)) --> FIL(m,n),
 (n_1517=n-1 & m=m_1530+1 & 1<=n & 0<=m_1530 & 
  FIL(m_1530,n_1517)) --> FIL(m,n),
 (n=0 & m=0) --> FIL(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: Some(emp&x'=null & n=0 & x'=x & v'=v&{FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [x]
 es_infer_vars_rel: [RMV]
 es_var_zero_perm: 

!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [RMV,x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 211::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&RMV(m,n)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 211::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&m>=1 & (m+
                              1)>=n & n>=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=n-1 & 2<=n) --> RMV(m,n),
 (n_1629=n-1 & m_1654=m-1 & 2<=n & 2<=m & RMV(m_1654,n_1629)) --> RMV(m,n),
 (n=1 & m=1) --> RMV(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 215::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]&
                                RMV2(m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 215::
                              EXISTS(m: res::ll<m>@M[Orig][LHSCase]&m>=0 & 
                              (m+1)>=n & n>=m&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (m=n-1 & 1<=n) --> RMV2(m,n),
 (n_1716=n-1 & m=m_1728+1 & 1<=n & 0<=m_1728 & 
  RMV2(m_1728,n_1716)) --> RMV2(m,n),
 (n=0 & m=0) --> RMV2(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 205::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]&
                                TRAV(m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 205::
                              EXISTS(m: x::ll<m>@M[Orig][LHSCase]&m>=0 & m=n&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n_1771=n-1 & m=m_1776+1 & 1<=n & 0<=m_1776 & 
  TRAV(m_1776,n_1771)) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_1793]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 163::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 163::ref [x]
                              EXISTS(G: G(x,x')&x=res&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&x'=x&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_164_919',next_164_920'>@L[Orig] * 
  HP_1793(next_164_920',x,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_1793(x',x,x) * x::node<val_164_1802,next_165_923'>@M[Orig]&
  v_node_166_924'=x&{FLOW,(22,23)=__norm}[]) --> G(x,x')&true&
  {FLOW,(22,23)=__norm}[]]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! es_infer_vars_hp_rel: [H,G]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 161::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 161::ref [x]
                              EXISTS(v',G: x'::node<v',x>@M[Orig] * G(x,x')&
                              v'=v&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x) * x'::node<v,x>@M[Orig]&true&{FLOW,(22,23)=__norm}[]) --> G(x,x')&
  true&{FLOW,(22,23)=__norm}[]]
Procedure push_front$node~int SUCCESS

Checking procedure reverse$node~node... 
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                    ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 192::ref [xs;ys]
                                EXISTS(k: ys'::ll<k>@M[Orig][LHSCase]&
                                REV(xs',k,m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)xs::ll<n>@M[Orig][LHSCase] * 
                  ys::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 192::ref [xs;ys]
                              EXISTS(k: ys'::ll<k>@M[Orig][LHSCase]&n>=0 & 
                              k>=n & xs'=null & k=m+n&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n_1837=n-1 & k_1856=k & m=m_1838-1 & 1<=n & 1<=m_1838 & 0<=k & 
  REV(xs',k_1856,m_1838,n_1837)) --> REV(xs',k,m,n),
 (n=0 & m=k & xs'=null & 0<=k) --> REV(xs',k,m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[i; j](ex)x::ll<i>@M[Orig][LHSCase] * 
                    y::ll<j>@M[Orig][LHSCase]&x!=null&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 168::
                                EXISTS(k: x::ll<k>@M[Orig][LHSCase]&SN(k,j)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i; j](ex)x::ll<i>@M[Orig][LHSCase] * 
                  y::ll<j>@M[Orig][LHSCase]&x!=null&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 168::
                              EXISTS(k: x::ll<k>@M[Orig][LHSCase]&j>=0 & j+
                              1=k&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (j=k-1 & 1<=k) --> SN(k,j)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
!!! es_infer_vars_hp_rel: [H,H1]
!!! es_infer_vars_hp_rel: [H,H1,HP_1969]
!!! es_infer_vars_hp_rel: [H,H1]
!!! es_infer_vars_hp_rel: [H,H1,HP_1969]
!!! OLD SPECS: ((None,[]),EInfer [SIZEH,H,H1]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 153::ref [n]
                                H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 153::ref [n]
                              EXISTS(H1: H1(x)&res>=n&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=res) --> SIZEH(res,n),
 (res=v_int_71_947' & SIZEH(v_int_71_947',1+n)) --> SIZEH(res,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&x=null&{FLOW,(22,23)=__norm}[]) --> H1(x)&true&{FLOW,(22,23)=__norm}[],
 (H(x)&x!=null&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_71_944',next_71_945'>@L[Orig] * 
  HP_1969(next_71_945',x)&true&{FLOW,(1,25)=__flow}[],
 (HP_1969(v_node_71_946',x) * x::node<val_71_1978,v_node_71_946'>@M[Orig]&
  x!=null&{FLOW,(22,23)=__norm}[]) --> H(v_node_71_946')&true&
  {FLOW,(22,23)=__norm}[],
 (x::node<val_71_1978,v_node_71_1983>@M[Orig]&x!=null&
  {FLOW,(22,23)=__norm}[]) --> H1(x)&true&{FLOW,(22,23)=__norm}[]]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! es_infer_vars_hp_rel: [T1,T2]
!!! es_infer_vars_hp_rel: [T1,T2]
!!! OLD SPECS: ((None,[]),EInfer [SIZE,T1,T2]
              EBase T1(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 157::
                                EXISTS(n: T2(x)&SIZE(res,n)&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase T1(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 157::
                              EXISTS(n: T2(x)&true&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (0<=res) --> SIZE(res,n_1995)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (T1(x)&true&{FLOW,(22,23)=__norm}[]) --> H(x)&true&{FLOW,(22,23)=__norm}[],
 (H1(x)&true&{FLOW,(22,23)=__norm}[]) --> T2(x)&true&{FLOW,(22,23)=__norm}[]]
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
!!! OLD SPECS: ((None,[]),EInfer [SPLICE]
              EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                    y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 233::ref [x]
                                EXISTS(t: x'::ll<t>@M[Orig][LHSCase]&
                                SPLICE(t,m,n)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::ll<n>@M[Orig][LHSCase] * 
                  y::ll<m>@M[Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 233::ref [x]
                              EXISTS(t: x'::ll<t>@M[Orig][LHSCase]&m>=0 & 
                              n>=0 & m+n=t&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=0 & m=t & 0<=t) --> SPLICE(t,m,n),
 (m_2052=m-1 & n_2051=n-1 & t=t_2063+2 & 1<=m & 1<=n & 0<=t_2063 & 
  SPLICE(t_2063,m_2052,n_2051)) --> SPLICE(t,m,n),
 (m=0 & t=n & 1<=n) --> SPLICE(t,m,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: 
  Some(emp&x'=null & n=0 & x'=x & a'=a & a'=1 & v_bool_351_773' & a'=a' & 
  v_bool_351_773'&{FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [n; a]
 es_infer_vars_rel: [SPLIT]
 es_var_zero_perm: 

!!! es_infer_vars_hp_rel: []locle1:  es_formula: hfalse&false&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: 
  Some(emp&x'=null & n=0 & x'=x & a!=1 & !(v_bool_351_773') & a!=1 & 
  !(v_bool_351_773') & a'+(1*1)=a&{FLOW,(22,23)=__norm}[])
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [n; a]
 es_infer_vars_rel: [SPLIT]
 es_var_zero_perm: 

!!! es_infer_vars_hp_rel: []
!!! OLD SPECS: ((None,[]),EInfer [SPLIT,n,a]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 198::ref [x]
                                EXISTS(n1,n2: x'::ll<n1>@M[Orig][LHSCase] * 
                                res::ll<n2>@M[Orig][LHSCase]&
                                SPLIT(n,a,n1,n2)&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&1<=a & a<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 198::ref [x]
                              EXISTS(n1,n2: x'::ll<n1>@M[Orig][LHSCase] * 
                              res::ll<n2>@M[Orig][LHSCase]&a>=1 & n2>=0 & 
                              a=n1 & a+n2=n&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n1=1 & a=1 & n2=n-1 & 1<=n) --> SPLIT(n,a,n1,n2),
 ((n2=0 & n1_2164=n1-1 & n_2136=n-1 & a=a'+1 & n2_2165=0 & 1<=n & 1<=n1 & 
  1<=a' | n1_2164=n1-1 & n_2136=n-1 & a=a'+1 & n2_2165=n2 & a'<=(0-1) & 
  1<=n & 0<=n2 & 1<=n1 | n1_2164=n1-1 & n_2136=n-1 & a=a'+1 & n2_2165=n2 & 
  1<=n & 1<=n2 & 1<=n1 & 1<=a') & 
  SPLIT(n_2136,a',n1_2164,n2_2165)) --> SPLIT(n,a,n1,n2)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! es_infer_vars_hp_rel: [H1,H2,G1,G2]
!!! OLD SPECS: ((None,[]),EInfer [H1,H2,G1,G2]
              EBase H1(x) * H2(y)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 158::ref [x;y]
                                G1(x,x') * G2(y,y')&true&
                                {FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H1(x) * H2(y)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 158::ref [x;y]
                              EXISTS(G1,G2: htrue * G1(x,x') * G2(y,y')&
                              x'=y & y'=x&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H1(x) * H2(y)&true&{FLOW,(22,23)=__norm}[]) --> G1(x,y) * G2(y,x)&true&
  {FLOW,(22,23)=__norm}[]]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 703 invocations 
2 false contexts at: ( (242,13)  (242,4) )

Total verification time: 1.9 second(s)
	Time spent in main process: 1.25 second(s)
	Time spent in child processes: 0.65 second(s)
