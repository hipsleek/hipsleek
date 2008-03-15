// @(#) $Id: TwoWayIterator.java,v 1.1.1.1 2008-03-15 06:55:00 nguyenh2 Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

// Author:  Clyde Ruby

package org.jmlspecs.samples.list.list2;

//@ refine "TwoWayIterator.jml";

//@ model import org.jmlspecs.models.JMLObjectBag;
import org.jmlspecs.models.JMLObjectSequence;

import org.jmlspecs.samples.list.node.OneWayNode;
import org.jmlspecs.samples.list.node.TwoWayNode;
import org.jmlspecs.samples.list.iterator.RestartableIterator;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class TwoWayIterator implements RestartableIterator {

    // data members
    protected TwoWayNode firstLink_;
    protected TwoWayNode currLink_;
    protected TwoWayNode lastLink_;

    public TwoWayIterator(TwoWayNode link) {
	firstLink_ = link;
	currLink_ = firstLink_;
	lastLink_ = firstLink_;
	first();
	while ( !isDone() ) {
	    lastLink_ = currLink_;
	    next();
	}
	first();
	// System.out.println("iterator:" + toString());
    }
    public void first() {
	// first node/link is a sentinel
	currLink_ = (TwoWayNode) firstLink_.getNextNode();
    }
    public void next() {
	currLink_ = (TwoWayNode) currLink_.getNextNode();
    }
    public /*@ pure @*/ boolean isDone() {
	return currLink_ == null;
    }
    public Object currentItem() {
	return currLink_.getEntry();
    }
    public void last() {
	currLink_ = lastLink_;
    }
    public void previous() {
	if (currLink_ == null) {
	    last();
	} else {
	    currLink_ = currLink_.getPrevNode();
	}
    }
    public /*@ pure @*/ boolean isAtFront() {
	if (currLink_ == null) {
	    return firstLink_.getNextNode() == null;
	} else {
	    return currLink_.getPrevNode() == firstLink_;
	}
    }

    // don't allow the default constructor
    protected TwoWayIterator() {
	firstLink_ = new TwoWayNode();
	currLink_ = firstLink_;
	lastLink_ = firstLink_;
	first();
	// System.out.println("iterator:" + toString());
    }
    public /*@ non_null @*/ String toString() {
	OneWayNode curr = firstLink_.getNextNode();
	String str = "";
	int index = 0;
	if (currLink_ == firstLink_) {
	    index = -1;
	    str += " || <";
	} else {
	    str += "<";
	    while (curr != currLink_) {
		str += curr.getEntry();
		if (curr.hasNext()) {
		    str += ", ";
		}
		curr = curr.getNextNode();
		index++;
	    }
	    str += " || ";
	}
	while (curr != null) {
	    str += curr.getEntry();
	    if (curr.hasNext()) {
		str += ", ";
	    }
	    curr = curr.getNextNode();
	}
	str += "> currIndex=" + index;
	return str;
    }
}

