// @(#)$Id: TwoWayIterator_JML_TestData.java,v 1.1.1.1 2008-03-15 06:55:00 nguyenh2 Exp $

// Copyright (C) 2004 Iowa State University

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

package org.jmlspecs.samples.list.list2;

import org.jmlspecs.models.JMLObjectSequence;
import org.jmlspecs.samples.list.node.TwoWayNode;
import org.jmlspecs.samples.list.iterator.RestartableIterator;

/** Supply test data for the JML and JUnit based testing of 
 *  TwoWayIterator.
 *
 *  <p>Test data is supplied by overriding methods in this class.  See
 *  the JML documentation and the comments below about how to do this.
 *
 *  <p>This class is also the place to override the <kbd>setUp()</kbd>
 *  and <kbd>tearDown()</kbd> methods if your testing needs some
 *  actions to be taken before and after each test is executed.
 *
 *  <p>This class is never rewritten by jmlunit.
 *
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public abstract class TwoWayIterator_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public TwoWayIterator_JML_TestData(java.lang.String name) {
        super(name);
    }

    /** Return the overall test suite for accumulating tests; the
     * result will hold every test that will be run.  This factory
     * method can be altered to provide filtering of test suites, as
     * they are added to this overall test suite, based on various
     * criteria.  The test driver will first call the method
     * addTestSuite to add a test suite formed from custom programmed
     * test methods (named testX for some X), which you can add to
     * this class; this initial test suite will also include a method
     * to check that the code being tested was compiled with jmlc.
     * After that, for each method to be tested, a test suite
     * containing tests for that method will be added to this overall
     * test suite, using the addTest method.  Test suites added for a
     * method will have some subtype of TestSuite and that method's
     * name as their name. So, if you want to control the overall
     * suite of tests for testing some method, e.g., to limit the
     * number of tests for each method, return a special-purpose
     * subclass of junit.framework.TestSuite in which you override the
     * addTest method.
     * @see junit.framework.TestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite overallTestSuite() {
        return new junit.framework.TestSuite("Overall tests for TwoWayIterator");
    }

    /** Return an empty test suite for accumulating tests for the
     * named method.  This factory method can be altered to provide
     * filtering or limiting of the tests for the named method, as
     * they are added to the test suite for this method.  The driver
     * will add individual tests using the addTest method.  So, if you
     * want to filter individual tests, return a subclass of TestSuite
     * in which you override the addTest method.
     * @param methodName The method the tests in this suite are for.
     * @see junit.framework.TestSuite
     * @see org.jmlspecs.jmlunit.strategies.LimitedTestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite emptyTestSuiteFor
        (java.lang.String methodName)
    {
        return new junit.framework.TestSuite(methodName);
    }

    // You should edit the following code to supply test data.  In the
    // skeleton originally supplied below the jmlunit tool made a
    // guess as to a minimal strategy for generating test data for
    // each type of object used as a receiver, and each type used as
    // an argument.  There is a library of strategies for generating
    // test data in org.jmlspecs.jmlunit.strategies, which are used in
    // the tool's guesses.  See the documentation for JML and in
    // particular for the org.jmlspecs.jmlunit.strategies package for
    // a general discussion of how to do this.  (This package's
    // documentation is available through the JML.html file in the top
    // of the JML release, and also in the package.html file that
    // ships with the package.)
    //
    // You can change the strategies guessed by the jmlunit tool, and
    // you can also define new ones to suit your needs.  You can also
    // delete any useless sample test data that has been generated
    // for you to show you the pattern of how to add your own test
    // data.  The only requirement is that you implement the methods
    // below.
    //
    // If you change the type being tested in a way that introduces
    // new types of arguments for some methods, then you will have to
    // introduce (by hand) definitions that are similar to the ones
    // below, because jmlunit never rewrites this file.

	TwoWayList[] list 
            = new TwoWayList[] {
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
                new TwoWayList(),
            };

    {
        list[1].insertBeforeCursor("it-r1");
        list[1].firstEntry();
        list[2].insertBeforeCursor("first2");
        list[2].firstEntry();
        list[2].insertAfterCursor("second2");
        list[2].append("third2");
        list[3].append("first3");
        list[3].append("second3");
        list[3].append("third3");
        list[3].append("fourth3");
        list[4].insertBeforeCursor(new int[1]);
        list[4].insertBeforeCursor(new int[2]);
        list[4].insertBeforeCursor(new int[3]);
        list[4].insertBeforeCursor(new int[4]);
        list[4].firstEntry();
        list[5].insertBeforeCursor("it-r5");
        list[5].decrementCursor();
        list[5].decrementCursor();
        list[6].insertBeforeCursor("it-r6");
        list[7].insertAfterCursor("L7");
    }

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.samples.list.list2.TwoWayIterator
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_samples_list_list2_TwoWayIteratorIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_samples_list_list2_TwoWayIteratorStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.samples.list.list2.TwoWayIterator. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_samples_list_list2_TwoWayIteratorStrategy
        = new org.jmlspecs.jmlunit.strategies.NewObjectAbstractStrategy()
            {
                protected Object make(int i) {
                    if (i <= 8) {
                        return list[i].createIterator();
                    } else {
                        switch (i) {
                        case 9:
			    TwoWayList list9 = (TwoWayList) list[0].clone();
                            TwoWayIterator iter9 = list9.createIterator();
                            return iter9;
                        case 10:
			    TwoWayList list10 = (TwoWayList) list[2].clone();
                            TwoWayIterator iter10 = list10.createIterator();
                            iter10.last();
                            iter10.next();
                            return iter10;
                        case 11:
			    TwoWayList list11 = (TwoWayList) list[3].clone();
                            TwoWayIterator iter11 = list11.createIterator();
                            iter11.last();
                            return iter11;
                        case 12:
                            return null;
                        default:
                            break;
                        }
                        throw new java.util.NoSuchElementException();
                    }
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.samples.list.node.TwoWayNode
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_samples_list_node_TwoWayNodeIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_samples_list_node_TwoWayNodeStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.samples.list.node.TwoWayNode. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_samples_list_node_TwoWayNodeStrategy
        = new org.jmlspecs.jmlunit.strategies.NewObjectAbstractStrategy()
            {
                protected Object make(int n) {
                    switch (n) {
                    case 0:
                        return null;
                    case 1:
                        return new TwoWayNode();
                    case 2:
                        TwoWayNode node0 = new TwoWayNode(null);
                        return node0;
                    case 3:
                        TwoWayNode node1 = new TwoWayNode(null);
                        node1.insertAfter(new TwoWayNode("it-n1"));
                        return node1;
                    case 4:
                        TwoWayNode node2 = new TwoWayNode(null);
                        node2.insertAfter("fourth-n2");
                        node2.insertAfter("third-n2");
                        node2.insertAfter("second-n2");
                        node2.insertAfter("first-n2");
                        return node2;
                    case 5:
                        TwoWayNode node3 = new TwoWayNode(null);
                        node3.insertAfter("first-n3");
                        node3.insertAfter("second-n3");
                        return node3;
                    case 6:
                        TwoWayNode node4 = new TwoWayNode(null);
                        node4.insertAfter("sixth-n4");
                        node4.insertAfter("fifth-n4");
                        return node4;
                    case 7:
                        TwoWayNode node5 = new TwoWayNode(null);
                        node5.insertAfter("eighth-n5");
                        node5.insertAfter("seventh-n5");
                        return node5;
                    case 8:
                        TwoWayNode node8 = new TwoWayNode(null);
                        node8.insertAfter("tenth-n8");
                        node8.insertAfter("ninth-n8");
                        return node8;
                    case 9:
                        TwoWayNode node7 = new TwoWayNode(null);
                        node7.insertAfter("9");
                        node7.insertAfter("8");
                        node7.insertAfter("7");
                        node7.insertAfter("6");
                        node7.insertAfter("5");
                        node7.insertAfter("4");
                        node7.insertAfter("3");
                        node7.insertAfter("2");
                        node7.insertAfter("1");
                        return node7;
                    default:
                        break;
                    }
                    throw new java.util.NoSuchElementException();
                }
            };
}
