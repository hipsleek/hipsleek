## $Id: Makefile.am,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $

bin_SCRIPTS = muh-check muh-rotatelog
data_DATA = muhrc
EXTRA_DIST = muhrc.in muh-check muh-rotatelog

install-dataDATA: $(data_DATA)
	@$(NORMAL_INSTALL)
	$(mkinstalldirs) $(DESTDIR)$(datadir)
	@if test $(ac_local) = yes; then \
	    chmod 700 $(DESTDIR)$(datadir) ; \
	fi
	@list='$(data_DATA)'; for p in $$list; do \
	    f=$(DESTDIR)$(datadir)/$$p ; \
	    if test $(ac_local) = yes; then \
	        if test -f $$f; then \
		    f=$$f.new ; \
		fi; \
	    fi; \
	    if test -f $(srcdir)/$$p ; then \
		$(INSTALL_DATA) $(srcdir)/$$p $$f ; \
	    else if test -f $$p; then \
		$(INSTALL_DATA) $$p $$f ; \
	    fi; fi; \
	done
