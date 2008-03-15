# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.1.1.1 2008-03-15 06:55:00 nguyenh2 Exp $

# Copyright (C) 1998, 1999 Iowa State University

# This file is part of JML

# JML is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.

# JML is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with JML; see the file COPYING.  If not, write to
# the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

#
# Developer's Makefile for testing JML specs
#

PACKAGE = org.jmlspecs.samples.list.list2

ITER_CLASSES_DIR = $(TOPDIR)/org/jmlspecs/samples/list/iterator
NODE_CLASSES_DIR = $(TOPDIR)/org/jmlspecs/samples/list/node

JAVAFILES = \
		OneWayList \
		E_OneWayList \
		TwoWayList \
		TwoWayIterator

NAMESTOTEST =	OneWayList E_OneWayList TwoWayList \
		TwoWayIterator

JML_REFINED_FILES = $(JAVAFILES:%=%.jml-refined)
JML_FILES = $(JAVAFILES:%=%.jml)

include ../Make.CommonDefs

# things should be done before static compiling
raccompile-static-before:
	$(MAKE) -C $(ITER_CLASSES_DIR) raccompile-static;
	$(MAKE) -C $(NODE_CLASSES_DIR) raccompile-static;

$(RAC_CLASSES_DIR)/raccompile.stamp:  $(JML_REFINED_FILES) $(JML_FILES)
