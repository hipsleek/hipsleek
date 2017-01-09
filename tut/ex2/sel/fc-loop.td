Q:={[n,m] -> [res] -> []: (((res=0 && n=0) && 0<=n) || ( (exists (fc_m_1392:( (exists (fc_n_1391:( (exists (v_int_24_1385:(v_int_24_1385+1=res && Q(fc_n_1391,fc_m_1392,v_int_24_1385))))  && fc_n_1391=n-(1))))  && fc_m_1392=m-(1))))  && 1<=n))
};
TD:=topdown(Q, 3, SimHeur);
TD;