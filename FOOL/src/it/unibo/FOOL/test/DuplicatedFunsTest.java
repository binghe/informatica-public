/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;

public class DuplicatedFunsTest extends UnitTest {
    @Test
    public void testDuplicatedArgs() {
	prog = "let int f(int x) 1; int f(int x) 1; in f(1);\n";
	try {
	    compile();
	} catch (Exception e) {
	    assertTrue(e instanceof RuntimeException);
	}
    }

    @Test
    public void testDuplicatedArgs2() {
	prog = "let int f(int x) x; int f(bool y) true; in f(5);\n";
	result = 5;
	trace = true;
	assertEquals(run(), result);
    }
}
