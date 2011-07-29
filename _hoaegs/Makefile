HIP=../hip
SLEEK=../sleek
HIPOPTS=-print -tp z3
SLKOPTS=-tp z3

allhip: hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9

allslk: hs1 hs2 hs3 hs4 hs5

hh0: hoahipex0.ss
	$(HIP) $(HIPOPTS) hoahipex0.ss >hh0.ssr

hh1: hoahipex1.ss
	$(HIP) $(HIPOPTS) hoahipex1.ss >hh1.ssr
	
hh2: hoahipex2.ss
	$(HIP) $(HIPOPTS) hoahipex2.ss >hh2.ssr
	
hh3: hoahipex3.ss
	$(HIP) $(HIPOPTS) hoahipex3.ss >hh3.ssr
	
hh4: hoahipex4.ss
	$(HIP) $(HIPOPTS) hoahipex4.ss >hh4.ssr
	
hh5: hoahipex5.ss
	$(HIP) $(HIPOPTS) hoahipex5.ss >hh5.ssr

hh6: hoahipex6.ss
	$(HIP) $(HIPOPTS) hoahipex6.ss >hh6.ssr
	
hh7: hoahipex7.ss
	$(HIP) $(HIPOPTS) hoahipex7.ss >hh7.ssr
	
hh8: hoahipex8.ss
	$(HIP) $(HIPOPTS) hoahipex8.ss >hh8.ssr
	
hh9: hoahipex9.ss
	$(HIP) $(HIPOPTS) hoahipex9.ss >hh9.ssr
	
hs1: hoaex1.slk
	$(SLEEK) $(SLKOPTS) hoaex1.slk >hs1.slkr
	
hs2: hoaex2.slk
	$(SLEEK) $(SLKOPTS) hoaex2.slk >hs2.slkr
	
hs3: hoaex3.slk
	$(SLEEK) $(SLKOPTS) hoaex3.slk >hs3.slkr
	
hs4: hoaex4.slk
	$(SLEEK) $(SLKOPTS) hoaex4.slk >hs4.slkr
	
hs5: hoaex5.slk
	$(SLEEK) $(SLKOPTS) hoaex5.slk >hs5.slkr
	
clean:
	rm *.ssr *.slkr
