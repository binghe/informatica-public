/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.assertTrue;
import org.junit.Test;

/* 
 * expected error: Duplicated variables found in current scope: x
 */

public final class DuplicatedArgsTest extends UnitTest {
    @Test
    public void testDuplicatedArgs() {
	prog = "let int f(int x, int x) 1; in f(1,2);\n";
	try {
	    compile();
	} catch (Exception e) {
	    assertTrue(e instanceof RuntimeException);
	}
    }
}
